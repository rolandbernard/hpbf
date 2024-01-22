use std::{env, fs::File, io::Read};

use hpbf::{parse, Context, Error, ErrorKind};

fn print_help_text() {
    println!(
        "Usage: {} [option].. [-f file].. [code]..",
        env::args().nth(0).unwrap()
    );
    println!("Options:");
    println!("   -f,--file file   Read the code from the given file");
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

fn main() -> Result<(), ()> {
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
                "-h" | "-help" | "--help" => print_help = true,
                "-f" | "-file" | "--file" => next_is_file = true,
                _ => code_segments.push(arg),
            }
        }
    }
    if print_help {
        print_help_text();
    } else {
        let mut cxt = Context::with_stdio();
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
    }
    return if has_error { Err(()) } else { Ok(()) };
}
