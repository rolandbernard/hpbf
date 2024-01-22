use std::{env, fs::File, io::Read};

use hpbf::{parse, CellType, Context, Error, ErrorKind};

fn print_help_text() {
    println!(
        "Usage: {} [option].. [-f file].. [code]..",
        env::args().nth(0).unwrap()
    );
    println!("Options:");
    println!("   -f,--file file   Read the code from the given file");
    println!("   -i8              Run the code using a cell size of 8 bit");
    println!("   -i16             Run the code using a cell size of 16 bit");
    println!("   -i32             Run the code using a cell size of 32 bit");
    println!("   -i64             Run the code using a cell size of 64 bit");
    println!("   -h,--help        Print this help text");
    println!("Arguments:");
    println!("   code             Execute the code given in the argument");
}

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
    }
}

fn execute_code<C: CellType>(code_segments: Vec<String>) -> bool {
    let mut has_error = false;
    let mut cxt = Context::<C>::with_stdio();
    for code in code_segments {
        match parse(&code) {
            Ok(program) => {
                if !has_error {
                    cxt.execute(&program)
                }
            }
            Err(error) => {
                print_error(&code, error);
                has_error = true;
            }
        }
    }
    return has_error;
}

fn main() -> Result<(), ()> {
    let mut bits = 8;
    let mut print_help = false;
    let mut has_error = false;
    let mut next_is_file = false;
    let mut code_segments = Vec::new();
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
                        code_segments.push(text);
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
                "-i8" => bits = 8,
                "-i16" => bits = 16,
                "-i32" => bits = 32,
                "-i64" => bits = 64,
                "-h" | "-help" | "--help" => print_help = true,
                "-f" | "-file" | "--file" => next_is_file = true,
                _ => code_segments.push(arg),
            }
        }
    }
    if print_help {
        print_help_text();
    } else {
        if match bits {
            8 => execute_code::<u8>(code_segments),
            16 => execute_code::<u16>(code_segments),
            32 => execute_code::<u32>(code_segments),
            64 => execute_code::<u64>(code_segments),
            _ => panic!("unsupported cell size"),
        } {
            has_error = true;
        }
    }
    return if has_error { Err(()) } else { Ok(()) };
}
