macro_rules! executor_tests {
    ($i:ident) => {
        #[cfg(test)]
        mod tests {
            use crate::{exec::{Executor, $i}, runtime::Context, Error};

            #[test]
            fn simple_execution() -> Result<(), Error<'static>> {
                let mut buf = Vec::new();
                let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
                // https://esolangs.org/wiki/Brainfuck#Examples
                let code = ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
                            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.";
                let exec = $i::<u8>::create(code, 2)?;
                exec.execute(&mut ctx)?;
                drop(ctx);
                assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
                Ok(())
            }

            #[test]
            fn simple_execution_u16() -> Result<(), Error<'static>> {
                let mut buf = Vec::new();
                let mut ctx = Context::<u16>::new(None, Some(Box::new(&mut buf)));
                // https://esolangs.org/wiki/Brainfuck#Examples
                let code = ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
                            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.";
                let exec = $i::<u16>::create(code, 2)?;
                exec.execute(&mut ctx)?;
                drop(ctx);
                assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
                Ok(())
            }

            #[test]
            fn simple_execution_u32() -> Result<(), Error<'static>> {
                let mut buf = Vec::new();
                let mut ctx = Context::<u32>::new(None, Some(Box::new(&mut buf)));
                // https://esolangs.org/wiki/Brainfuck#Examples
                let code = ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
                            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.";
                let exec = $i::<u32>::create(code, 2)?;
                exec.execute(&mut ctx)?;
                drop(ctx);
                assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
                Ok(())
            }

            #[test]
            fn simple_execution_u64() -> Result<(), Error<'static>> {
                let mut buf = Vec::new();
                let mut ctx = Context::<u64>::new(None, Some(Box::new(&mut buf)));
                // https://esolangs.org/wiki/Brainfuck#Examples
                let code = ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
                            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.";
                let exec = $i::<u64>::create(code, 2)?;
                exec.execute(&mut ctx)?;
                drop(ctx);
                assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
                Ok(())
            }

            #[test]
            #[cfg_attr(miri, ignore)]
            fn test_program_access_distant_cell() -> Result<(), Error<'static>> {
                let mut buf = Vec::new();
                let mut ctx = Context::<u64>::new(None, Some(Box::new(&mut buf)));
                // https://brainfuck.org/tests.b
                let code = "++++[>++++++<-]>[>+++++>+++++++<<-]>>++++<[[>[[
                            >>+<<-]<]>>>-]>-[>+>+<<-]>]+++++[>+++++++<<++>-]>.<<.";
                let exec = $i::<u64>::create(code, 2)?;
                exec.execute(&mut ctx)?;
                drop(ctx);
                assert_eq!(String::from_utf8(buf).unwrap(), "#\n");
                Ok(())
            }

            #[test]
            fn test_program_output_h() -> Result<(), Error<'static>> {
                let mut buf = Vec::new();
                let mut ctx = Context::<u64>::new(None, Some(Box::new(&mut buf)));
                // https://brainfuck.org/tests.b
                let code = "[]++++++++++[>>+>+>++++++[<<+<+++>>>-]<<<<-]
                            \"A*$\";?@![#>>+<<]>[>>]<<<<[>++<[-]]>.>.";
                let exec = $i::<u64>::create(code, 2)?;
                exec.execute(&mut ctx)?;
                drop(ctx);
                assert_eq!(String::from_utf8(buf).unwrap(), "H\n");
                Ok(())
            }

            #[test]
            #[cfg_attr(miri, ignore)]
            fn test_program_rot13() -> Result<(), Error<'static>> {
                let mut buf = Vec::new();
                let mut ctx = Context::<u8>::new(
                    Some(Box::new("~mlk zyx".as_bytes())),
                    Some(Box::new(&mut buf)),
                );
                // https://brainfuck.org/rot13.b
                let code = ",
                    [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
                    [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
                    [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
                    [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
                    [>++++++++++++++<-
                    [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
                    [>>+++++[<----->-]<<-
                    [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
                    [>++++++++++++++<-
                    [>+<-[>+<-[>+<-[>+<-[>+<-
                    [>++++++++++++++<-
                    [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
                    [>>+++++[<----->-]<<-
                    [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
                    [>++++++++++++++<-
                    [>+<-]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
                    ]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]>.[-]<,]";
                let exec = $i::<u8>::create(code, 2)?;
                exec.execute(&mut ctx)?;
                drop(ctx);
                assert_eq!(String::from_utf8(buf).unwrap(), "~zyx mlk");
                Ok(())
            }
        }
    };
}

// The following are not actually unused, but the compiler seems to think it is.
#[allow(unused_macros)]
macro_rules! same_as_inplace_test_inner {
    ($i:ident, $c:expr) => {
        let code = $c;
        let mut input = Vec::new();
        for i in 0..1024 {
            input.push((183 * i) as u8);
        }
        let mut out_inplace = input.clone();
        let mut out_to_test = input.clone();
        let mut ctx_inplace = Context::<u8>::new(
            Some(Box::new(&input[..])),
            Some(Box::new(&mut out_inplace[..])),
        );
        let mut ctx_to_test = Context::<u8>::new(
            Some(Box::new(&input[..])),
            Some(Box::new(&mut out_to_test[..])),
        );
        InplaceInterpreter::<u8>::create(code, 3)?.execute(&mut ctx_inplace)?;
        $i::<u8>::create(code, 3)?.execute(&mut ctx_to_test)?;
        drop(ctx_inplace);
        drop(ctx_to_test);
        assert_eq!(out_to_test, out_inplace);
        return Ok(());
    };
}

#[allow(unused_macros)]
macro_rules! same_as_inplace_test {
    ($i:ident, $c:expr, $n:ident) => {
        #[test]
        fn $n() -> Result<(), Error<'static>> {
            same_as_inplace_test_inner!($i, $c);
        }
    };
}

#[allow(unused_macros)]
macro_rules! same_as_inplace_test_no_miri {
    ($i:ident, $c:expr, $n:ident) => {
        #[test]
        #[cfg_attr(miri, ignore)]
        fn $n() -> Result<(), Error<'static>> {
            same_as_inplace_test_inner!($i, $c);
        }
    };
}

macro_rules! same_as_inplace_tests {
    ($i:ident) => {
        #[cfg(test)]
        mod tests_same_as_inplace {
            use crate::{exec::{Executor, InplaceInterpreter, $i}, runtime::Context, Error};

            // Test cases that have previously caused issues found using fuzzing.
            same_as_inplace_test!($i, "<+[-..+]", infinite_loop_with_canceling_cond);
            same_as_inplace_test!($i, "+>-[[...<..>[.]].]", no_return_reading_two_cells);
            same_as_inplace_test!($i, "--.[.[+<->.]<]-+", muladd_must_be_performed_before_loop);
            same_as_inplace_test!($i, "[-->-<-.]..-<+.[.]", loop_elimination);
            same_as_inplace_test!($i, ",-[.]", infinite_loop_depending_on_input);
            same_as_inplace_test!($i, ",.[>.[.]>+.<]>-[.]", loop_elimination_inside_if);
            same_as_inplace_test!($i, "<+[<,->+.]<[+.<]", pending_add_after_input);
            same_as_inplace_test!($i, "+>-<[>,<+.]>-[.]", add_overwritten_by_input_in_loop);
            same_as_inplace_test!($i, "+>+[[[<.]+.]-<.]", nested_infinite_loop);
            same_as_inplace_test!($i, "--<,[+>,<...]>..", input_controlled_loop_taken);
            same_as_inplace_test!(
                $i,
                "--<,,,,,,,-[+>,<...]>..",
                input_controlled_loop_not_taken
            );
            same_as_inplace_test!($i, ",-[+<[->..].]>-[.]", moving_if);
            same_as_inplace_test!($i, ">>+,,.[<[.]+.-].", loop_to_if_pending_cond_preservation);
            same_as_inplace_test!(
                $i,
                "+>+[<-[.]+.>]<->",
                canceling_cond_after_loop_elimination
            );
            same_as_inplace_test!($i, "--[[>+<.[-,>>>.]-[+<<.]<]+>->>.]", non_optimizable);
            same_as_inplace_test!($i, "-+,+[,>,,.[.<-.]-<[[<.]<+[.].]>]", non_optimizable2);
            same_as_inplace_test!(
                $i,
                ",-[,[-<,.+>>><-.+[.]].+[.][.]<<]",
                ifs_do_not_guarantee_zero_of_cond
            );
            same_as_inplace_test!($i, "-+,+<,[>.[-]+.]", infinite_moving_loop);
            same_as_inplace_test!($i, "[[[-]--[.].]-.]->.,.<.", nested_no_return_in_if);
            same_as_inplace_test!($i, ".-[>+<[>[-].].]", inlining_non_read_but_written);
            same_as_inplace_test!($i, "-[-],--+,.><->++<[[<[-].]+[>.].]", shift_in_loop);
            same_as_inplace_test!(
                $i,
                ",+>+[[,<[+].]+[.-++].+]",
                simple_loop_after_shifted_inline
            );
            same_as_inplace_test!(
                $i,
                "+++[[.,<<.[+]]-.[..+]]",
                inlined_loop_after_shifted_inline
            );
            same_as_inplace_test!(
                $i,
                "+[[>[,-,-.].]-[<->.[.]].]",
                inlined_loop_with_loop_motion
            );
            same_as_inplace_test!($i, "+[-,[,<,>,.]-<[+.-,]->.]", maybe_read_maybe_not);
            same_as_inplace_test!($i, "+[[<<+>[+]>-],<<.]", loop_elimination_inside_if2);
            same_as_inplace_test!($i, "->[.]<[.[->-<]]>[.]", zeroing_cond_written_in_loop);
            same_as_inplace_test!(
                $i,
                "-[.[<[-].<><>>[-<->]]-[<.]]",
                pending_depends_on_other_pending
            );
            same_as_inplace_test!(
                $i,
                "[+]>+[<[>-<+]->>.<]",
                non_changing_in_first_loop_but_not_const
            );
            same_as_inplace_test!(
                $i,
                "+[<<>.->]",
                no_effect_still_needs_clobbering
            );
            same_as_inplace_test!(
                $i,
                "+.->-[<+[,.]>-]",
                non_clobbering_writes_are_still_needed
            );
            same_as_inplace_test!(
                $i,
                "+[.,>+[.>[.]]+[.[-<>.,]]]",
                loop_analysis_after_inlining_shift
            );
            same_as_inplace_test!(
                $i,
                ",[<]+[+[+[-.[-]]]].",
                non_clobbering_writes_must_be_recorded
            );
            same_as_inplace_test!(
                $i,
                ",>,>-<<[>>+<<-]>[<+>-]>[<+>-]<.",
                dependent_pending_operations
            );

            // Manually created test cases.
            same_as_inplace_test_no_miri!(
                $i,
                "+[,>,>,>[-]>[-]>[-]<<<<<[>[>>+>+<<<-]>>>[<<<+>>>-]<<<<-]>[>
                [>+>+<<-]>>[<<+>>-]<<<-]>>[>+<-]>[-[>+<<++>-]<+>>[<+>-]<]<+
                +[>+<-]>[-[>+<<++>-]<+>>[<+>-]<]<++[>+<-]>[-[>+<<++>-]<+>>[
                <+>-]<]<++[>+<-]>[-[>+<<++>-]<+>>[<+>-]<]<.<<<[-]+]",
                very_large_polynomial
            );
        }
    };
}
