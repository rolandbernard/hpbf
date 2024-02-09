use std::{
    collections::hash_map::RandomState,
    env, fs,
    hash::{BuildHasher, Hasher},
    path::Path,
    time::{Duration, Instant, SystemTime},
};

use hpbf::{BaseInterpreter, CellType, Context, Executor, InplaceInterpreter};

/// Generate a random Brainfuck program. The program is guaranteed to be syntactically
/// valid and additionally contains at least one output instruction per loop.
fn generate_code(hasher: &mut impl Hasher, max_len: usize) -> String {
    let mut str = String::new();
    let mut missing_outs = 0;
    let mut stack = Vec::new();
    while str.len() + stack.len() + missing_outs < max_len {
        hasher.write_usize(str.len());
        match hasher.finish() % 8 {
            0 => str.push('+'),
            1 => str.push('-'),
            2 => str.push('<'),
            3 => str.push('>'),
            4 => str.push(','),
            5 => {
                str.push('.');
                if let Some(v) = stack.last_mut() {
                    if *v {
                        missing_outs -= 1;
                    }
                    *v = false;
                }
            }
            6 => {
                if stack.is_empty() {
                    str.push('[');
                    stack.push(true);
                    missing_outs += 1;
                } else {
                    if stack.pop().unwrap() {
                        str.push('.');
                        missing_outs -= 1;
                    }
                    str.push(']');
                }
            }
            _ => {
                str.push('[');
                stack.push(true);
                missing_outs += 1;
            }
        }
    }
    for missing_out in stack.into_iter().rev() {
        if missing_out {
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
        input.push(i as u8);
    }
    let mut output = vec![0; 1024];
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
    let baseint_no_opt = result_with::<u8, BaseInterpreter<u8>>(code, false, 0);
    if inplace != baseint_no_opt {
        return false;
    }
    let baseint = result_with::<u8, BaseInterpreter<u8>>(code, true, 1);
    if inplace != baseint {
        return false;
    }
    let baseint_opt3 = result_with::<u8, BaseInterpreter<u8>>(code, true, 3);
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
        let random = RandomState::new();
        let mut last = Instant::now();
        let mut hasher = random.build_hasher();
        for i in 0.. {
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
