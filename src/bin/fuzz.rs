//! Small application that performs fuzzing on the optimizer by comparing it to
//! the inplace interpreter.

use std::{
    collections::{hash_map::RandomState, HashMap, HashSet},
    env, fs,
    hash::{BuildHasher, DefaultHasher, Hash, Hasher},
    path::Path,
    time::{Duration, Instant},
};

use hpbf::{
    exec::{BaseInterpreter, Executor, InplaceInterpreter},
    runtime::Context,
    CellType,
};

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

    /// After introducing an `+` instruction.
    fn add(&mut self) {
        if let Some(v) = self.known_loads.get_mut(&self.shift) {
            *v = v.wrapping_add(1);
        } else if !self.written.contains(&self.shift) {
            let v = self.known_adds.entry(self.shift).or_insert(0);
            *v = v.wrapping_add(1);
        }
    }

    /// After introducing an `-` instruction.
    fn sub(&mut self) {
        if let Some(v) = self.known_loads.get_mut(&self.shift) {
            *v = v.wrapping_sub(1);
        } else if !self.written.contains(&self.shift) {
            let v = self.known_adds.entry(self.shift).or_insert(0);
            *v = v.wrapping_sub(1);
        }
    }

    /// After introducing an `<` instruction.
    fn left(&mut self) {
        self.shift -= 1;
    }

    /// After introducing an `>` instruction.
    fn right(&mut self) {
        self.shift += 1;
    }

    /// After introducing an `,` instruction.
    fn input(&mut self) {
        self.written.insert(self.shift);
        self.known_adds.remove(&self.shift);
        self.known_loads.remove(&self.shift);
    }

    /// After introducing an `.` instruction.
    fn output(&mut self) {
        self.has_out = true;
    }

    /// After introducing an `[` instruction.
    fn push(&mut self) -> Self {
        let initial_cond = self.known_loads.get(&self.shift).copied();
        GenState::new(initial_cond)
    }

    /// After introducing an `]` instruction.
    fn pop(&mut self, prev_state: Self) -> bool {
        let mut needs_out = false;
        if prev_state.initial_cond != Some(0) {
            if !prev_state.finite() && !prev_state.has_out {
                needs_out = true
            }
            if prev_state.sub_shift || prev_state.shift != 0 {
                self.sub_shift = true;
                self.written.clear();
                self.known_adds.clear();
                self.known_loads.clear();
            } else {
                for &var in prev_state
                    .known_adds
                    .keys()
                    .chain(prev_state.known_loads.keys())
                    .chain(prev_state.written.iter())
                {
                    let var = self.shift + var;
                    self.written.insert(var);
                    self.known_adds.remove(&var);
                    self.known_loads.remove(&var);
                }
            }
            if prev_state.initial_cond.is_some() {
                if prev_state.has_out {
                    self.has_out = true;
                }
                for (&var, &val) in &prev_state.known_loads {
                    self.known_loads
                        .insert(self.shift + var - prev_state.shift, val);
                }
            }
        }
        self.written.remove(&self.shift);
        self.known_adds.remove(&self.shift);
        self.known_loads.insert(self.shift, 0);
        needs_out
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
                state.add();
            }
            1 => {
                str.push('-');
                state.sub();
            }
            2 => {
                str.push('<');
                state.left();
            }
            3 => {
                str.push('>');
                state.right();
            }
            4 => {
                str.push(',');
                state.input();
            }
            5 => {
                str.push('.');
                state.output();
            }
            6 => {
                if stack.len() > 1 {
                    let prev_state = stack.pop().unwrap();
                    let state = stack.last_mut().unwrap();
                    if state.pop(prev_state) {
                        str.push('.');
                    }
                    str.push(']');
                }
            }
            _ => {
                str.push('[');
                let new = state.push();
                stack.push(new);
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
fn result_with<'code, C: CellType, E: Executor<'code, C>>(code: &'code str, opt: u32) -> Vec<u8> {
    let mut input = Vec::new();
    for i in 0..1024 {
        input.push((183 * i) as u8);
    }
    let mut output = input.clone();
    let mut context = Context::new(Some(Box::new(&input[..])), Some(Box::new(&mut output[..])));
    let exec = E::create(code, opt).unwrap();
    exec.execute(&mut context).unwrap();
    drop(context);
    return output;
}

/// Check the code by executing it with different executors. Tests that the output
/// of all the executors is identical.
fn check_code<'code>(code: &'code str) -> bool {
    let inplace = result_with::<u8, InplaceInterpreter<'code, u8>>(code, 0);
    let baseint_no_opt = result_with::<u8, BaseInterpreter<u8>>(code, 0);
    if inplace != baseint_no_opt {
        return false;
    }
    let irint = result_with::<u8, BaseInterpreter<u8>>(code, 4);
    if inplace != irint {
        return false;
    }
    return true;
}

/// Code is "safe" if there is a finite amount of operations executed between
/// each IO operation.
fn is_safe(code: &str) -> bool {
    let mut stack = vec![GenState::new(Some(0))];
    for inst in code.chars() {
        let state = stack.last_mut().unwrap();
        match inst {
            '+' => state.add(),
            '-' => state.sub(),
            '<' => state.left(),
            '>' => state.right(),
            ',' => state.input(),
            '.' => state.output(),
            ']' => {
                if stack.len() > 1 {
                    let prev_state = stack.pop().unwrap();
                    let state = stack.last_mut().unwrap();
                    if state.pop(prev_state) {
                        return false;
                    }
                }
            }
            '[' => {
                let new = state.push();
                stack.push(new);
            }
            _ => { /* comment */ }
        }
    }
    return true;
}

/// Delete some random instructions such that the code still fails.
fn minimize_code(hasher: &mut impl Hasher, code: String) -> String {
    hasher.write_usize(code.len());
    let code_bytes = code.as_bytes();
    for i in (0..code.len())
        .cycle()
        .skip(hasher.finish() as usize % code.len())
        .take(code.len())
    {
        let next;
        if code_bytes[i] == b']' {
            let mut start = i - 1;
            let mut cnt = 0;
            loop {
                if code_bytes[start] == b'[' {
                    if cnt == 0 {
                        break;
                    }
                    cnt -= 1;
                } else if code_bytes[start] == b']' {
                    cnt += 1;
                }
                start -= 1;
            }
            next = code[..start].to_owned() + &code[start + 1..i] + &code[i + 1..];
        } else if code_bytes[i] == b'[' {
            let mut end = i + 1;
            let mut cnt = 0;
            loop {
                if code_bytes[end] == b']' {
                    if cnt == 0 {
                        break;
                    }
                    cnt -= 1;
                } else if code_bytes[end] == b'[' {
                    cnt += 1;
                }
                end += 1;
            }
            next = code[..i].to_owned() + &code[end + 1..];
        } else {
            next = code[..i].to_owned() + &code[i + 1..];
        }
        if is_safe(&next) && !check_code(&next) {
            return minimize_code(hasher, next);
        }
    }
    return code;
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
    println!("   --minimize file    Run the example in file and try to make it smaller");
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
    let mut minimize = None;
    let mut max_len = 64;
    let mut next_is_dir = false;
    let mut next_is_len = false;
    let mut next_is_min = false;
    for arg in env::args().skip(1) {
        if next_is_dir {
            directory = arg;
        } else if next_is_min {
            minimize = Some(arg);
        } else if next_is_len {
            if let Ok(v) = arg.parse::<usize>() {
                max_len = v;
            } else {
                eprintln!("{arg}: ignoring invalid length");
            }
        } else {
            match arg.as_str() {
                "--recheck" => recheck = true,
                "--minimize" => next_is_min = true,
                "-d" | "--dir" => next_is_dir = true,
                "-m" | "--max-len" => next_is_len = true,
                "-h" | "-help" | "--help" => print_help = true,
                _ => eprintln!("{arg}: ignoring unknown argument"),
            }
        }
    }
    if print_help {
        print_help_text();
    } else if let Some(file) = minimize {
        let dir = Path::new(&directory);
        let content = fs::read_to_string(file).unwrap();
        loop {
            let random = RandomState::new();
            let mut hasher = random.build_hasher();
            for i in 0..100_000 {
                hasher.write_usize(i);
                let code = minimize_code(&mut hasher, content.clone());
                let mut hasher = DefaultHasher::new();
                code.hash(&mut hasher);
                let path = dir.join(hasher.finish().to_string() + ".bf");
                fs::write(path, code).unwrap();
            }
        }
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
                    let code = minimize_code(&mut hasher, code);
                    let mut hasher = DefaultHasher::new();
                    code.hash(&mut hasher);
                    let path = dir.join(hasher.finish().to_string() + ".bf");
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
