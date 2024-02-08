//! Main application that allows execution of Brainfuck programs.

use std::{env, fs::File, io::Read, process::exit};

use hpbf::{BaseInterpreter, CellType, Context, Error, ErrorKind, Executor, InplaceInterpreter};

enum ExecutorKind {
    Inplace,
    BaseInt,
}

/// Print the CLI help text for this program to stdout.
fn print_help_text() {
    println!(
        "Usage: {} [option].. [-f file].. [code]..",
        env::args().nth(0).unwrap()
    );
    println!("Options:");
    println!("   -f,--file file   Read the code from the given file");
    println!("   --print-ir       Print ir code to stdout and do not execute");
    println!("   --inplace        Use the inplace non-optimizing interpreter");
    println!("   --base-int       Use the baseline slightly optimizing interpreter");
    println!("   --no-opt         Apply only the minimum optimizations required");
    println!("   -O{{0|1|2|3|4}}    Apply different levels of optimization");
    println!("   -i8              Run the code using a cell size of 8 bit");
    println!("   -i16             Run the code using a cell size of 16 bit");
    println!("   -i32             Run the code using a cell size of 32 bit");
    println!("   -i64             Run the code using a cell size of 64 bit");
    println!("   -h,--help        Print this help text");
    println!("Arguments:");
    println!("   code             Execute the code given in the argument");
}

/// Print the given `error` for the given `code` to stderr.
fn print_error(error: Error) {
    match error.kind {
        ErrorKind::LoopNotClosed => {
            eprintln!("error: unbalances brackets, loop not closed");
        }
        ErrorKind::LoopNotOpened => {
            eprintln!("error: unbalanced brackets, loop not opened");
        }
        ErrorKind::FileReadFailed => {
            eprintln!("error: failed to open file `{}`", error.str);
        }
        ErrorKind::FileEncodingError => {
            eprintln!("error: failed to read file `{}`", error.str);
        }
        ErrorKind::LlvmError => {
            eprintln!("error: llvm error: {}", error.str);
        }
    }
}

/// Parse, optimize, and execute the given code with the given optimization
/// level and options. Alternatively, if `print_ir` is true, do not execute,
/// but only print the final IR.
fn execute_code<C: CellType>(
    code: &str,
    print_ir: bool,
    kind: ExecutorKind,
    no_opt: bool,
    opt: u32,
) -> Result<(), Error> {
    if print_ir {
        let exec = BaseInterpreter::<C>::create(code, no_opt, opt)?;
        exec.print_ir();
    } else {
        let mut cxt = Context::<C>::with_stdio();
        match kind {
            ExecutorKind::Inplace => {
                let exec = InplaceInterpreter::<C>::create(code, no_opt, opt)?;
                exec.execute(&mut cxt)?;
            }
            ExecutorKind::BaseInt => {
                let exec = BaseInterpreter::<C>::create(code, no_opt, opt)?;
                exec.execute(&mut cxt)?;
            }
        }
    }
    Ok(())
}

fn main() {
    let mut bits = 8;
    let mut print_help = false;
    let mut print_ir = false;
    let mut kind = ExecutorKind::BaseInt;
    let mut no_opt = false;
    let mut opt = 1;
    let mut has_error = false;
    let mut next_is_file = false;
    let mut code = String::new();
    for arg in env::args().skip(1) {
        if next_is_file {
            next_is_file = false;
            match File::open(&arg) {
                Ok(mut file) => {
                    if let Err(_) = file.read_to_string(&mut code) {
                        print_error(Error {
                            kind: ErrorKind::FileEncodingError,
                            str: &arg,
                            position: 0,
                        });
                        has_error = true;
                    }
                }
                Err(_) => {
                    print_error(Error {
                        kind: ErrorKind::FileReadFailed,
                        str: &arg,
                        position: 0,
                    });
                    has_error = true;
                }
            }
        } else {
            match arg.as_str() {
                "--print-ir" => print_ir = true,
                "--inplace" => kind = ExecutorKind::Inplace,
                "--base-int" => kind = ExecutorKind::BaseInt,
                "--no-opt" => no_opt = true,
                "-O0" => opt = 0,
                "-O1" => opt = 1,
                "-O2" => opt = 2,
                "-O3" => opt = 3,
                "-O4" => opt = 4,
                "-i8" => bits = 8,
                "-i16" => bits = 16,
                "-i32" => bits = 32,
                "-i64" => bits = 64,
                "-h" | "-help" | "--help" => print_help = true,
                "-f" | "-file" | "--file" => next_is_file = true,
                _ => code.push_str(&arg),
            }
        }
    }
    if print_help {
        print_help_text();
    } else if !has_error {
        if let Err(error) = match bits {
            8 => execute_code::<u8>(&code, print_ir, kind, no_opt, opt),
            16 => execute_code::<u16>(&code, print_ir, kind, no_opt, opt),
            32 => execute_code::<u32>(&code, print_ir, kind, no_opt, opt),
            64 => execute_code::<u64>(&code, print_ir, kind, no_opt, opt),
            _ => panic!("unsupported cell size"),
        } {
            print_error(error);
            has_error = true;
        }
    }
    if has_error {
        exit(1)
    } else {
        exit(0)
    };
}
