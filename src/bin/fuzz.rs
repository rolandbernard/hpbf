use std::{
    collections::{hash_map::RandomState, HashMap, HashSet},
    env, fs,
    hash::{BuildHasher, Hasher},
    path::Path,
    time::{Duration, Instant, SystemTime},
};

use hpbf::{BaseInterpreter, CellType, Context, Executor, InplaceInterpreter};

/// State used to track variable information during the code generation for the
/// fuzzing. This is required to ensure that every loop is either finite or performs
/// some kind of output.
struct GenState {
    shift: isize,
    sub_shift: bool,
    has_out: bool,
    initial_cond: Option<u64>,
    written: HashSet<isize>,
    known_loads: HashMap<isize, u64>,
    known_adds: HashMap<isize, u64>,
}

impl GenState {
    /// Create a new state with initial values.
    fn new(initial_cond: Option<u64>) -> Self {
        GenState {
            shift: 0,
            sub_shift: false,
            has_out: false,
            initial_cond,
            written: HashSet::new(),
            known_loads: HashMap::new(),
            known_adds: HashMap::new(),
        }
    }

    /// Return true if the loop is guaranteed to run a finite number of times.
    /// Note that this by itself does not guarantee that the loop will ever
    /// complete, e.g. if a contained loop is not finite.
    fn finite(&self) -> bool {
        if self.initial_cond == Some(0) {
            true
        } else if let Some(v) = self.known_loads.get(&self.shift) {
            *v == 0
        } else if self.sub_shift || self.shift != 0 {
            false
        } else if let Some(v) = self.known_adds.get(&0) {
            v.is_odd()
        } else {
            false
        }
    }
}

/// Generate a random Brainfuck program. The program is guaranteed to be syntactically
/// valid and additionally guarantees that loops are either finite or print some output.
fn generate_code(hasher: &mut impl Hasher, max_len: usize) -> String {
    let mut str = String::new();
    let mut stack = vec![GenState::new(Some(0))];
    while str.len() + 2 * (stack.len() - 1) < max_len {
        hasher.write_usize(str.len());
        let state = stack.last_mut().unwrap();
        match hasher.finish() % 8 {
            0 => {
                str.push('+');
                if let Some(v) = state.known_loads.get_mut(&state.shift) {
                    *v = v.wrapping_add(1);
                } else if !state.written.contains(&state.shift) {
                    let v = state.known_adds.entry(state.shift).or_insert(0);
                    *v = v.wrapping_add(1);
                }
            }
            1 => {
                str.push('-');
                if let Some(v) = state.known_loads.get_mut(&state.shift) {
                    *v = v.wrapping_sub(1);
                } else if !state.written.contains(&state.shift) {
                    let v = state.known_adds.entry(state.shift).or_insert(0);
                    *v = v.wrapping_sub(1);
                }
            }
            2 => {
                str.push('<');
                state.shift -= 1;
            }
            3 => {
                str.push('>');
                state.shift += 1;
            }
            4 => {
                str.push(',');
                state.written.insert(state.shift);
                state.known_adds.remove(&state.shift);
                state.known_loads.remove(&state.shift);
            }
            5 => {
                str.push('.');
                state.has_out = true;
            }
            6 => {
                if stack.len() > 1 {
                    let prev_state = stack.pop().unwrap();
                    if !prev_state.finite() && !prev_state.has_out {
                        str.push('.');
                    }
                    str.push(']');
                    let state = stack.last_mut().unwrap();
                    if prev_state.initial_cond != Some(0) {
                        if prev_state.sub_shift || prev_state.shift != 0 {
                            state.sub_shift = true;
                            state.written.clear();
                            state.known_adds.clear();
                            state.known_loads.clear();
                        } else {
                            for &var in prev_state
                                .known_adds
                                .keys()
                                .chain(prev_state.known_loads.keys())
                                .chain(prev_state.written.iter())
                            {
                                let var = state.shift + var;
                                state.written.insert(var);
                                state.known_adds.remove(&var);
                                state.known_loads.remove(&var);
                            }
                        }
                        if prev_state.initial_cond.is_some() {
                            if prev_state.has_out {
                                state.has_out = true;
                            }
                            for (&var, &val) in &prev_state.known_loads {
                                state
                                    .known_loads
                                    .insert(state.shift + var - prev_state.shift, val);
                            }
                        }
                    }
                }
            }
            _ => {
                str.push('[');
                let initial_cond = state.known_loads.get(&state.shift).copied();
                stack.push(GenState::new(initial_cond));
            }
        }
    }
    for state in stack.into_iter().skip(1).rev() {
        if !state.finite() && !state.has_out {
            str.push('.');
        }
        str.push(']');
    }
    return str;
}

/// Execute the code and terminate after either reading or writing a certain
/// finite number of bytes. Returns the output bytes as a [`Vec<u8>`].
fn result_with<'code, C: CellType, E: Executor<'code, C>>(
    code: &'code str,
    no_opt: bool,
    opt: u32,
) -> Vec<u8> {
    let mut input = Vec::new();
    for i in 0..1024 {
        input.push((183 * i) as u8);
    }
    let mut output = input.clone();
    let mut context = Context::new(Some(Box::new(&input[..])), Some(Box::new(&mut output[..])));
    let exec = E::create(code, no_opt, opt).unwrap();
    exec.execute(&mut context).unwrap();
    drop(context);
    return output;
}

/// Check the code by executing it with different executors. Tests that the output
/// of all the executors is identical.
fn check_code<'code>(code: &'code str) -> bool {
    let inplace = result_with::<u8, InplaceInterpreter<'code, u8>>(code, false, 0);
    let baseint_no_opt = result_with::<u8, BaseInterpreter<u8>>(code, true, 0);
    if inplace != baseint_no_opt {
        return false;
    }
    let baseint = result_with::<u8, BaseInterpreter<u8>>(code, false, 1);
    if inplace != baseint {
        return false;
    }
    let baseint_opt3 = result_with::<u8, BaseInterpreter<u8>>(code, false, 3);
    if inplace != baseint_opt3 {
        return false;
    }
    return true;
}

/// Print the current number of successful and failed code samples.
fn print_status(success: usize, failure: usize) {
    println!("success: {success}, failure: {failure}");
}

/// Print the CLI help text for this program to stdout.
fn print_help_text() {
    println!("Usage: {} [option]", env::args().nth(0).unwrap());
    println!("Options:");
    println!("   --recheck          Run again all the stored failed examples");
    println!("   -d,--dir dir       Store or load failed examples in this directory");
    println!("   -m,--max-len len   Don't generate code longer that len bytes");
    println!("   -h,--help          Print this help text");
}

fn main() {
    let mut success = 0;
    let mut failure = 0;
    let mut print_help = false;
    let mut recheck = false;
    let mut directory = "fuzz-errors".to_owned();
    let mut max_len = 64;
    let mut next_is_dir = false;
    let mut next_is_len = false;
    for arg in env::args().skip(1) {
        if next_is_dir {
            directory = arg;
        } else if next_is_len {
            if let Ok(v) = arg.parse::<usize>() {
                max_len = v;
            } else {
                eprintln!("{arg}: ignoring invalid length");
            }
        } else {
            match arg.as_str() {
                "--recheck" => recheck = true,
                "-d" | "--dir" => next_is_dir = true,
                "-m" | "--max-len" => next_is_len = true,
                "-h" | "-help" | "--help" => print_help = true,
                _ => eprintln!("{arg}: ignoring unknown argument"),
            }
        }
    }
    if print_help {
        print_help_text();
    } else if recheck {
        let dir = Path::new(&directory);
        let mut last = Instant::now();
        for file in fs::read_dir(dir).unwrap() {
            let file = file.unwrap().path();
            let code = fs::read_to_string(&file).unwrap();
            if check_code(&code) {
                success += 1;
                fs::remove_file(file).unwrap();
            } else {
                failure += 1;
            }
            let now = Instant::now();
            if now.duration_since(last) > Duration::from_secs(2) {
                print_status(success, failure);
                last = now;
            }
        }
        print_status(success, failure);
    } else {
        let dir = Path::new(&directory);
        fs::create_dir_all(dir).unwrap();
        loop {
            let random = RandomState::new();
            let mut last = Instant::now();
            let mut hasher = random.build_hasher();
            for i in 0..100_000 {
                hasher.write_usize(i);
                let code = generate_code(&mut hasher, max_len);
                if check_code(&code) {
                    success += 1;
                } else {
                    failure += 1;
                    let timestamp = SystemTime::now();
                    let path = dir.join(
                        timestamp
                            .duration_since(SystemTime::UNIX_EPOCH)
                            .unwrap()
                            .as_nanos()
                            .to_string()
                            + ".bf",
                    );
                    fs::write(path, code).unwrap();
                }
                let now = Instant::now();
                if now.duration_since(last) > Duration::from_secs(2) {
                    print_status(success, failure);
                    last = now;
                }
            }
        }
    }
}
