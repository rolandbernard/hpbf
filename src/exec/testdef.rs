macro_rules! executor_tests {
    ($i:ident) => {
        #[cfg(test)]
        mod tests {
            use crate::{$i, Context, Error, Executor};

            #[test]
            fn simple_execution() -> Result<(), Error> {
                let mut buf = Vec::new();
                let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
                let code = ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
                            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.";
                let exec = $i::<u8>::create(code, false, 1)?;
                exec.execute(&mut ctx)?;
                drop(ctx);
                assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
                Ok(())
            }

            #[test]
            fn simple_execution_u16() -> Result<(), Error> {
                let mut buf = Vec::new();
                let mut ctx = Context::<u16>::new(None, Some(Box::new(&mut buf)));
                let code = ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
                            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.";
                let exec = $i::<u16>::create(code, false, 1)?;
                exec.execute(&mut ctx)?;
                drop(ctx);
                assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
                Ok(())
            }

            #[test]
            fn simple_execution_u32() -> Result<(), Error> {
                let mut buf = Vec::new();
                let mut ctx = Context::<u32>::new(None, Some(Box::new(&mut buf)));
                let code = ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
                            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.";
                let exec = $i::<u32>::create(code, false, 1)?;
                exec.execute(&mut ctx)?;
                drop(ctx);
                assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
                Ok(())
            }

            #[test]
            fn simple_execution_u64() -> Result<(), Error> {
                let mut buf = Vec::new();
                let mut ctx = Context::<u64>::new(None, Some(Box::new(&mut buf)));
                let code = ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
                            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.";
                let exec = $i::<u64>::create(code, false, 1)?;
                exec.execute(&mut ctx)?;
                drop(ctx);
                assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
                Ok(())
            }

            #[test]
            #[cfg_attr(miri, ignore)]
            fn test_program_access_distant_cell() -> Result<(), Error> {
                let mut buf = Vec::new();
                let mut ctx = Context::<u64>::new(None, Some(Box::new(&mut buf)));
                let code = "++++[>++++++<-]>[>+++++>+++++++<<-]>>++++<[[>[[
                            >>+<<-]<]>>>-]>-[>+>+<<-]>]+++++[>+++++++<<++>-]>.<<.";
                let exec = $i::<u64>::create(code, false, 1)?;
                exec.execute(&mut ctx)?;
                drop(ctx);
                assert_eq!(String::from_utf8(buf).unwrap(), "#\n");
                Ok(())
            }

            #[test]
            fn test_program_output_h() -> Result<(), Error> {
                let mut buf = Vec::new();
                let mut ctx = Context::<u64>::new(None, Some(Box::new(&mut buf)));
                let code = "[]++++++++++[>>+>+>++++++[<<+<+++>>>-]<<<<-]
                            \"A*$\";?@![#>>+<<]>[>>]<<<<[>++<[-]]>.>.";
                let exec = $i::<u64>::create(code, false, 1)?;
                exec.execute(&mut ctx)?;
                drop(ctx);
                assert_eq!(String::from_utf8(buf).unwrap(), "H\n");
                Ok(())
            }

            #[test]
            #[cfg_attr(miri, ignore)]
            fn test_program_rot13() -> Result<(), Error> {
                let mut buf = Vec::new();
                let mut ctx = Context::<u8>::new(
                    Some(Box::new("~mlk zyx".as_bytes())),
                    Some(Box::new(&mut buf)),
                );
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
                let exec = $i::<u8>::create(code, false, 1)?;
                exec.execute(&mut ctx)?;
                drop(ctx);
                assert_eq!(String::from_utf8(buf).unwrap(), "~zyx mlk");
                Ok(())
            }
        }
    };
}
