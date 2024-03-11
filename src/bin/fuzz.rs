//! Small application that performs fuzzing on the optimizer by comparing it to
//! the inplace interpreter.

use std::{
    collections::hash_map::RandomState,
    env, fs,
    hash::{BuildHasher, DefaultHasher, Hash, Hasher},
    path::Path,
    time::{Duration, Instant},
};

use hpbf::{
    exec::{BaseJitCompiler, BcInterpreter, Executor, InplaceInterpreter, IrInterpreter},
    runtime::Context,
    CellType,
};

/// Generate a random Brainfuck program. The program is guaranteed to be syntactically
/// valid and additionally guarantees that loops are either finite or print some output.
fn generate_code(hasher: &mut impl Hasher, max_len: usize) -> String {
    let mut str = String::new();
    let mut open = 0;
    while str.len() + open < max_len {
        hasher.write_usize(str.len());
        match hasher.finish() % 8 {
            0 => str.push('+'),
            1 => str.push('-'),
            2 => str.push('<'),
            3 => str.push('>'),
            4 => str.push(','),
            5 => str.push('.'),
            6 => {
                if open > 1 {
                    open -= 1;
                    str.push(']');
                }
            }
            _ => {
                str.push('[');
                open += 1
            }
        }
    }
    for _ in 0..open {
        str.push(']');
    }
    return str;
}

/// Execute the code and terminate after either reading or writing a certain
/// finite number of bytes. Returns the output bytes as a [`Vec<u8>`].
fn result_with<'code, C: CellType, E: Executor<'code, C>>(
    code: &'code str,
    opt: u32,
) -> (bool, Vec<u8>) {
    let mut input = Vec::new();
    for i in 0..1024 {
        input.push((183 * i) as u8);
    }
    let mut output = Vec::new();
    let mut context = Context::new(Some(Box::new(&input[..])), Some(Box::new(&mut output)));
    let exec = E::create(code, opt).unwrap();
    let finished = exec.execute_limited(&mut context, 1_000).unwrap();
    drop(context);
    return (finished, output);
}

/// Compare that the two execution results. Since the execution might have been
/// interrupted at different times, this only checks the parts that are present
/// in both, unless the programs finished.
fn compare_results(a: &(bool, Vec<u8>), b: &(bool, Vec<u8>)) -> bool {
    if a.0 && b.0 {
        a.1 == b.1
    } else {
        if a.0 && a.1.len() < b.1.len() {
            return false;
        }
        if b.0 && b.1.len() < a.1.len() {
            return false;
        }
        for i in 0..a.1.len().min(b.1.len()) {
            if a.1[i] != b.1[i] {
                return false;
            }
        }
        return true;
    }
}

/// Check the code by executing it with different executors. Tests that the output
/// of all the executors is identical.
fn check_code<'code, C: CellType>(code: &'code str) -> bool {
    let inplace = result_with::<C, InplaceInterpreter<'code, C>>(code, 0);
    let irint0 = result_with::<C, IrInterpreter<C>>(code, 0);
    if !compare_results(&inplace, &irint0) {
        return false;
    }
    let irint1 = result_with::<C, IrInterpreter<C>>(code, 1);
    if !compare_results(&inplace, &irint1) || !compare_results(&irint0, &irint1) {
        return false;
    }
    let irint2 = result_with::<C, IrInterpreter<C>>(code, 4);
    if !compare_results(&inplace, &irint2) || !compare_results(&irint1, &irint2) {
        return false;
    }
    let bcint0 = result_with::<C, BcInterpreter<C>>(code, 0);
    if !compare_results(&inplace, &bcint0) || !compare_results(&irint2, &bcint0) {
        return false;
    }
    let bcint1 = result_with::<C, BcInterpreter<C>>(code, 1);
    if !compare_results(&inplace, &bcint1)
        || !compare_results(&irint2, &bcint1)
        || !compare_results(&bcint0, &bcint1)
    {
        return false;
    }
    let bcint2 = result_with::<C, BcInterpreter<C>>(code, 4);
    if !compare_results(&inplace, &bcint2)
        || !compare_results(&irint2, &bcint2)
        || !compare_results(&bcint1, &bcint2)
    {
        return false;
    }
    let bcjit2 = result_with::<C, BaseJitCompiler<C>>(code, 4);
    if !compare_results(&inplace, &bcjit2)
        || !compare_results(&irint2, &bcjit2)
        || !compare_results(&bcint2, &bcjit2)
    {
        return false;
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
        .filter(|&i| code_bytes[i] == b'[')
        .chain(
            (0..code.len())
                .cycle()
                .skip(hasher.finish() as usize % code.len())
                .take(code.len()),
        )
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
        if !check_code::<u8>(&next) {
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
            if check_code::<u8>(&code) {
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
                if check_code::<u8>(&code) {
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
