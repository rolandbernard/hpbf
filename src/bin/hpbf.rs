//! Main application that allows execution of Brainfuck programs.

use std::{env, fs::File, io::Read, process::exit};

use hpbf::{
    bc,
    exec::{BcInterpreter, Executor, InplaceInterpreter, IrInterpreter},
    ir,
    runtime::Context,
    CellType, Error, ErrorKind,
};

/// The kind of executor to use.
enum ExecutorKind {
    PrintIr,
    PrintBc,
    Inplace,
    IrInt,
    BcInt,
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
    println!("   --print-bc       Print byte code to stdout and do not execute");
    println!("   --inplace        Use the inplace non-optimizing interpreter");
    println!("   --ir-int         Use the internal IR interpreter");
    println!("   --bc-int         Use the optimizing bytecode interpreter");
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
fn execute_code<C: CellType>(code: &str, kind: ExecutorKind, opt: u32) -> Result<(), Error> {
    let mut cxt = Context::<C>::with_stdio();
    match kind {
        ExecutorKind::PrintIr => {
            let program = ir::Program::<C>::parse(code)?;
            let program = program.optimize(opt);
            println!("{program:?}");
        }
        ExecutorKind::PrintBc => {
            let program = ir::Program::<C>::parse(code)?;
            let program = program.optimize(opt);
            let bytecode = bc::CodeGen::translate(&program, 2);
            println!("{bytecode:?}");
        }
        ExecutorKind::Inplace => {
            let exec = InplaceInterpreter::<C>::create(code, opt)?;
            exec.execute(&mut cxt)?;
        }
        ExecutorKind::IrInt => {
            let exec = IrInterpreter::<C>::create(code, opt)?;
            exec.execute(&mut cxt)?;
        }
        ExecutorKind::BcInt => {
            let exec = BcInterpreter::<C>::create(code, opt)?;
            exec.execute(&mut cxt)?;
        }
    }
    Ok(())
}

fn main() {
    let mut bits = 8;
    let mut print_help = false;
    let mut kind = ExecutorKind::BcInt;
    let mut opt = 2;
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
                "--print-ir" => kind = ExecutorKind::PrintIr,
                "--print-bc" => kind = ExecutorKind::PrintBc,
                "--inplace" => kind = ExecutorKind::Inplace,
                "--ir-int" => kind = ExecutorKind::IrInt,
                "--bc-int" => kind = ExecutorKind::BcInt,
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
            8 => execute_code::<u8>(&code, kind, opt),
            16 => execute_code::<u16>(&code, kind, opt),
            32 => execute_code::<u32>(&code, kind, opt),
            64 => execute_code::<u64>(&code, kind, opt),
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
