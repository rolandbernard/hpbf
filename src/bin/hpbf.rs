//! Main application that allows execution of Brainfuck programs.

use std::{env, fs::File, io::Read, process::exit};

use hpbf::{CellType, Context, Error, ErrorKind, Program};

/// Print the CLI help text for this program to stdout.
fn print_help_text() {
    println!(
        "Usage: {} [option].. [-f file].. [code]..",
        env::args().nth(0).unwrap()
    );
    println!("Options:");
    println!("   -f,--file file   Read the code from the given file");
    println!("   --no-jit         Do not perform jit compilation");
    println!("   --print-ir       Print ir code to stderr and do not execute");
    println!("   --no-opt         Do not apply any pre-llvm optimization");
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
fn print_error(code: &str, error: Error) {
    match error.kind {
        ErrorKind::LoopNotClosed => {
            eprintln!("error: unbalances brackets, loop not closed");
        }
        ErrorKind::LoopNotOpened => {
            eprintln!("error: unbalanced brackets, loop not opened");
        }
        ErrorKind::FileReadFailed => {
            eprintln!("error: failed to open file `{code}`");
        }
        ErrorKind::FileEncodingError => {
            eprintln!("error: failed to read file `{code}`");
        }
        ErrorKind::LlvmError => {
            eprintln!("error: llvm error: {code}");
        }
    }
}

/// Fallback using the interpreter when the `llvm` feature is disabled.
#[cfg(not(feature = "llvm"))]
fn execute_in_context<C: CellType>(
    cxt: &mut Context<C>,
    _opt: u32,
    prog: Program<C>,
    print_ir: bool,
) -> bool {
    if print_ir {
        eprintln!("{:#?}", prog);
    } else {
        cxt.execute(&prog);
    }
    return false;
}

/// Execute a given program `prog` in the given context `cxt` using the JIT
/// compiler. This function is replaced with the interpreter if the `llvm`
/// feature is not enabled.
#[cfg(feature = "llvm")]
fn execute_in_context<C: CellType>(
    cxt: &mut Context<C>,
    opt: u32,
    prog: Program<C>,
    print_ir: bool,
) -> bool {
    if let Err(str) = if print_ir {
        cxt.jit_print_module(opt, &prog)
    } else {
        cxt.jit_execute(opt, &prog)
    } {
        print_error(
            &str,
            Error {
                kind: ErrorKind::LlvmError,
                position: 0,
            },
        );
        return true;
    }
    return false;
}

/// Parse, optimize, and execute the given code with the given optimization
/// level and options. Alternatively, if `print_ir` is true, do not execute,
/// but only print the final IR.
fn execute_code<C: CellType>(
    code: String,
    no_opt: bool,
    opt: u32,
    no_jit: bool,
    print_ir: bool,
) -> bool {
    match Program::parse(&code) {
        Ok(program) => {
            let prog = if no_opt { program } else { program.optimize() };
            let mut cxt = Context::<C>::with_stdio();
            if no_jit {
                if print_ir {
                    eprintln!("{:#?}", prog);
                } else {
                    cxt.execute(&prog);
                }
                return false;
            } else {
                return execute_in_context(&mut cxt, opt, prog, print_ir);
            }
        }
        Err(error) => {
            print_error(&code, error);
            return true;
        }
    }
}

fn main() {
    let mut bits = 8;
    let mut print_help = false;
    let mut no_jit = true;
    let mut print_ir = false;
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
                    let mut text = String::new();
                    if let Err(_) = file.read_to_string(&mut text) {
                        print_error(
                            &arg,
                            Error {
                                kind: ErrorKind::FileEncodingError,
                                position: 0,
                            },
                        );
                        has_error = true;
                    } else {
                        code.push_str(&text);
                    }
                }
                Err(_) => {
                    print_error(
                        &arg,
                        Error {
                            kind: ErrorKind::FileReadFailed,
                            position: 0,
                        },
                    );
                    has_error = true;
                }
            }
        } else {
            match arg.as_str() {
                "--no-jit" => no_jit = true,
                "--print-ir" => print_ir = true,
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
    } else {
        if match bits {
            8 => execute_code::<u8>(code, no_opt, opt, no_jit, print_ir),
            16 => execute_code::<u16>(code, no_opt, opt, no_jit, print_ir),
            32 => execute_code::<u32>(code, no_opt, opt, no_jit, print_ir),
            64 => execute_code::<u64>(code, no_opt, opt, no_jit, print_ir),
            _ => panic!("unsupported cell size"),
        } {
            has_error = true;
        }
    }
    if has_error {
        exit(1)
    } else {
        exit(0)
    };
}
