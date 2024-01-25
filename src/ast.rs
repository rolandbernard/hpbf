//! Contains parsing and optimizing transformations for a Brainfuck program.

use std::collections::{HashMap, HashSet};

use crate::{CellType, Error, ErrorKind};

/// Represents a complete Brainfuck program or inside of a loop.
pub type Block<C> = Vec<Instr<C>>;

/// This represents a Brainfuck instruction. It includes not only the basic
/// Brainfuck instructions, but also some additional operations that are common
/// in Brainfuck and help the backend to generate better code.
#[derive(Clone, PartialEq, Debug)]
pub enum Instr<C: CellType> {
    Move(isize),
    Load(C, isize),
    Add(C, isize),
    MulAdd(C, isize, isize),
    Output(isize),
    Input(isize),
    Loop(isize, Block<C>),
}

/// Parses a string containing a Brainfuck program into an internal
/// representation. This will already cluster sequential increment, decrement,
/// and movement instructions.
///
/// # Examples
/// ```
/// # use hpbf::{parse, Error, Instr};
/// use Instr::*;
///
/// let prog = parse::<u8>("+[-->-[>>+>-----<<]<--<---]>-.>>>+.>>..+++[.>]<<<<.+++.------.<<-.>>>>+.")?;
///
/// assert_eq!(prog, vec![
///     Add(1, 0),
///     Loop(0, vec![
///         Add(254, 0), Move(1), Add(255, 0),
///         Loop(0, vec![Move(2), Add(1, 0), Move(1), Add(251, 0), Move(-2)]),
///         Move(-1), Add(254, 0), Move(-1), Add(253, 0),
///     ]),
///     Move(1), Add(255, 0), Output(0), Move(3), Add(1, 0), Output(0),
///     Move(2), Output(0), Output(0), Add(3, 0),
///     Loop(0, vec![Output(0), Move(1)]),
///     Move(-4), Output(0), Add(3, 0), Output(0), Add(250, 0), Output(0),
///     Move(-2), Add(255, 0), Output(0), Move(4), Add(1, 0), Output(0),
/// ]);
/// # Ok::<(), Error>(())
/// ```
pub fn parse<C: CellType>(program: &str) -> Result<Block<C>, Error> {
    let mut blocks = vec![Block::<C>::new()];
    let mut positions = vec![];
    for (i, char) in program.chars().enumerate() {
        let block = blocks.last_mut().unwrap();
        match char {
            '>' => {
                if let Some(Instr::Move(i)) = block.last_mut() {
                    *i += 1;
                } else {
                    block.push(Instr::Move(1));
                }
            }
            '<' => {
                if let Some(Instr::Move(i)) = block.last_mut() {
                    *i -= 1;
                } else {
                    block.push(Instr::Move(-1));
                }
            }
            '+' => {
                if let Some(Instr::Add(i, 0)) = block.last_mut() {
                    *i = i.wrapping_add(C::ONE);
                } else {
                    block.push(Instr::Add(C::ONE, 0));
                }
            }
            '-' => {
                if let Some(Instr::Add(i, 0)) = block.last_mut() {
                    *i = i.wrapping_add(C::NEG_ONE);
                } else {
                    block.push(Instr::Add(C::NEG_ONE, 0));
                }
            }
            '.' => {
                block.push(Instr::Output(0));
            }
            ',' => {
                block.push(Instr::Input(0));
            }
            '[' => {
                positions.push(i);
                blocks.push(Block::new());
            }
            ']' => {
                if positions.len() == 0 {
                    return Err(Error {
                        kind: ErrorKind::LoopNotOpened,
                        position: i,
                    });
                } else {
                    positions.pop();
                    let instr = Instr::Loop(0, blocks.pop().unwrap());
                    blocks.last_mut().unwrap().push(instr);
                }
            }
            _ => { /* comment */ }
        }
    }
    if blocks.len() == 1 {
        return Ok(blocks.remove(0));
    } else {
        return Err(Error {
            kind: ErrorKind::LoopNotClosed,
            position: *positions.last().unwrap(),
        });
    }
}

/// Enum used for constant value propagation in the optimizer.
enum OptimizerValue<C> {
    UnknownValue,
    UnknownAddition { pending: C },
    KnownValue { value: C, pending: bool },
    KnownAddition { value: C, pending: C },
}

/// Struct that holds the information during the analysis of a single block.
struct OptimizerContext<C> {
    ptr: isize,
    assume_zero: bool,
    had_shift: bool,
    cell_values: HashMap<isize, OptimizerValue<C>>,
    read_cells: HashSet<isize>,
    written_cells: HashSet<isize>,
}

/// Enum representing the analysis result on the number of time a loop will run.
enum OptimizerLoopCount<C: CellType> {
    Unknown,
    Finite,
    Simple,
    SimpleNegated,
    AtLeastOnce,
    AtMostOnce,
    NeverOrInfinite,
    Infinite,
    NTimes(C),
}

impl<C: CellType> OptimizerLoopCount<C> {
    /// Returns wether the loop is guaranteed to never execute.
    fn never(&self) -> bool {
        match self {
            OptimizerLoopCount::NTimes(c) if *c == C::ZERO => true,
            _ => false,
        }
    }

    /// Returns wether the loop is executed at least once.
    fn at_least_once(&self) -> bool {
        match self {
            OptimizerLoopCount::AtLeastOnce => true,
            OptimizerLoopCount::Infinite => true,
            OptimizerLoopCount::NTimes(c) if *c != C::ZERO => true,
            _ => false,
        }
    }

    /// Returns wether the loop is executed at most once.
    fn at_most_once(&self) -> bool {
        match self {
            OptimizerLoopCount::AtMostOnce => true,
            OptimizerLoopCount::NTimes(c) if *c == C::ZERO || *c == C::ONE => true,
            _ => false,
        }
    }

    /// Returns wether the loops effects will be visible to the code following
    /// the loop. This can be false if the loop is either never run or if the
    /// loop is guaranteed to never terminate.
    fn effects_seen_later(&self) -> bool {
        match self {
            OptimizerLoopCount::NeverOrInfinite => false,
            OptimizerLoopCount::Infinite => false,
            OptimizerLoopCount::NTimes(c) if *c == C::ZERO => false,
            _ => true,
        }
    }

    /// Returns true if the loop is guaranteed to be executed a finite number of times.
    fn is_finite(&self) -> bool {
        match self {
            OptimizerLoopCount::Finite => true,
            OptimizerLoopCount::Simple => true,
            OptimizerLoopCount::SimpleNegated => true,
            OptimizerLoopCount::AtMostOnce => true,
            OptimizerLoopCount::NTimes(_) => true,
            _ => false,
        }
    }
}

impl<C: CellType> OptimizerContext<C> {
    /// Create a new context for optimization.
    fn new(assume_zero: bool, ptr: isize) -> Self {
        OptimizerContext::<C> {
            ptr,
            assume_zero,
            had_shift: false,
            cell_values: HashMap::new(),
            read_cells: HashSet::new(),
            written_cells: HashSet::new(),
        }
    }

    /// Emit (if necessary) the buffered modifications to the cell indicated by
    /// `src` and write the instructions into `block`.
    fn emit(&mut self, src: isize, block: &mut Block<C>) {
        match self.cell_values.get_mut(&src) {
            Some(OptimizerValue::KnownValue { value, pending }) if *pending => {
                block.push(Instr::Load(*value, src));
                *pending = false;
                self.written_cells.insert(src);
            }
            Some(
                OptimizerValue::KnownAddition { pending, .. }
                | OptimizerValue::UnknownAddition { pending },
            ) if *pending != C::ZERO => {
                block.push(Instr::Add(*pending, src));
                *pending = C::ZERO;
                self.read_cells.insert(src);
                self.written_cells.insert(src);
            }
            _ => {
                if !self.written_cells.contains(&src) {
                    self.read_cells.insert(src);
                }
            }
        }
    }

    /// Emit (if necessary) the buffered changes for all cells in `to_emit`.
    fn emit_all(&mut self, to_emit: &[isize], block: &mut Block<C>) {
        for &cell in to_emit {
            self.emit(cell, block);
        }
    }

    /// Return all cells for which some changes are pending.
    fn pending(&self) -> Vec<isize> {
        self.cell_values
            .iter()
            .filter(|(_, v)| match v {
                OptimizerValue::KnownValue { pending, .. } if *pending => true,
                OptimizerValue::KnownAddition { pending, .. }
                | OptimizerValue::UnknownAddition { pending }
                    if *pending != C::ZERO =>
                {
                    true
                }
                _ => false,
            })
            .map(|(k, _)| *k)
            .collect()
    }

    /// Return all cells for which the original value, that existed in them
    /// before the execution of the block, has been read.
    fn read(&self) -> Vec<isize> {
        self.read_cells.iter().copied().collect()
    }

    /// Analyze the behavior of a loop with condition cell `cond` and for which
    /// `sub_cxt` has finished the optimization analysis.
    fn compute_loop_count(&self, cond: isize, sub_cxt: &Self) -> OptimizerLoopCount<C> {
        if self.ptr != sub_cxt.ptr || sub_cxt.had_shift {
            OptimizerLoopCount::Unknown
        } else if let Some(OptimizerValue::KnownValue { value, .. }) = self.cell_values.get(&cond) {
            if *value == C::ZERO {
                OptimizerLoopCount::NTimes(C::ZERO)
            } else {
                match sub_cxt.cell_values.get(&cond) {
                    Some(OptimizerValue::KnownValue { value, .. }) => {
                        if *value == C::ZERO {
                            OptimizerLoopCount::NTimes(C::ONE)
                        } else {
                            OptimizerLoopCount::Infinite
                        }
                    }
                    Some(OptimizerValue::KnownAddition { value: inc, .. }) => {
                        if let Some(n) = value.wrapping_div(inc.wrapping_neg()) {
                            OptimizerLoopCount::NTimes(n)
                        } else {
                            OptimizerLoopCount::Infinite
                        }
                    }
                    Some(_) => OptimizerLoopCount::AtLeastOnce,
                    None => OptimizerLoopCount::Infinite,
                }
            }
        } else {
            match sub_cxt.cell_values.get(&cond) {
                Some(OptimizerValue::KnownValue { value, .. }) => {
                    if *value == C::ZERO {
                        OptimizerLoopCount::AtMostOnce
                    } else {
                        OptimizerLoopCount::NeverOrInfinite
                    }
                }
                Some(OptimizerValue::KnownAddition { value: inc, .. }) => {
                    if *inc == C::NEG_ONE {
                        OptimizerLoopCount::Simple
                    } else if *inc == C::ONE {
                        OptimizerLoopCount::SimpleNegated
                    } else if *inc == C::ZERO {
                        OptimizerLoopCount::NeverOrInfinite
                    } else if inc.is_odd() {
                        OptimizerLoopCount::Finite
                    } else {
                        OptimizerLoopCount::Unknown
                    }
                }
                Some(_) => OptimizerLoopCount::Unknown,
                None => OptimizerLoopCount::NeverOrInfinite,
            }
        }
    }

    /// Process a [`Instr::Load`] instruction.
    fn load_cell(&mut self, dst: isize, val: C) {
        match self
            .cell_values
            .entry(dst)
            .or_insert(OptimizerValue::UnknownValue)
        {
            a @ (OptimizerValue::UnknownValue
            | OptimizerValue::UnknownAddition { .. }
            | OptimizerValue::KnownAddition { .. }) => {
                *a = OptimizerValue::KnownValue {
                    value: val,
                    pending: true,
                };
            }
            OptimizerValue::KnownValue { value, pending } => {
                if *value != val {
                    *value = val;
                    *pending = true;
                }
            }
        }
    }

    /// Process a [`Instr::Add`] instruction.
    fn add_cell(&mut self, dst: isize, val: C) {
        if val != C::ZERO {
            match self.cell_values.entry(dst).or_insert(if self.assume_zero {
                OptimizerValue::KnownValue {
                    value: C::ZERO,
                    pending: false,
                }
            } else {
                OptimizerValue::KnownAddition {
                    value: C::ZERO,
                    pending: C::ZERO,
                }
            }) {
                a @ OptimizerValue::UnknownValue => {
                    *a = OptimizerValue::UnknownAddition { pending: val };
                }
                OptimizerValue::KnownValue { value, pending } => {
                    *value = value.wrapping_add(val);
                    *pending = true;
                }
                OptimizerValue::KnownAddition { pending, value } => {
                    *value = value.wrapping_add(val);
                    *pending = pending.wrapping_add(val);
                }
                OptimizerValue::UnknownAddition { pending } => {
                    *pending = pending.wrapping_add(val);
                }
            }
        }
    }

    /// Process a [`Instr::MulAdd`] instruction.
    fn add_mul_cell(&mut self, dst: isize, val: C, src: isize, block: &mut Block<C>) {
        if val != C::ZERO {
            match self.cell_values.get(&src) {
                Some(OptimizerValue::KnownValue { value, .. }) => {
                    self.add_cell(dst, value.wrapping_mul(val))
                }
                _ => {
                    block.push(Instr::MulAdd(val, src, dst));
                    self.cell_values.insert(dst, OptimizerValue::UnknownValue);
                    self.read_cells.insert(src);
                    self.written_cells.insert(src);
                }
            }
        }
    }

    /// Process a [`Instr::Loop`] instruction.
    fn loop_on(&mut self, cond: isize, sub_block: Block<C>, block: &mut Block<C>) {
        let mut sub_cxt = Self::new(false, self.ptr);
        let mut sub_block = sub_cxt.optimize_block(sub_block);
        let iters = self.compute_loop_count(cond, &sub_cxt);
        if !iters.never() {
            let ptr_shift = sub_cxt.ptr - self.ptr;
            if ptr_shift != 0 || sub_cxt.had_shift {
                // If the location of cells might have been shifted, we are
                // unable to perform any other optimization.
                sub_cxt.emit_all(&sub_cxt.pending(), &mut sub_block);
                if ptr_shift != 0 {
                    sub_block.push(Instr::Move(ptr_shift));
                }
                self.emit_all(&self.pending(), block);
                block.push(Instr::Loop(cond, sub_block));
                self.had_shift = true;
                self.assume_zero = false;
                self.cell_values.clear();
                self.read_cells.clear();
                self.written_cells.clear();
            } else {
                sub_cxt.emit_all(&sub_cxt.read(), &mut sub_block);
                self.emit_all(&sub_cxt.read(), block);
                let mut to_add = Block::new();
                for var in sub_cxt.pending() {
                    if var != cond {
                        if let Some(OptimizerValue::KnownAddition { value, .. }) =
                            sub_cxt.cell_values.get(&var)
                        {
                            if iters.at_most_once() {
                                if iters.at_least_once() {
                                    self.add_cell(var, *value);
                                } else {
                                    self.emit(var, block);
                                    to_add.push(Instr::Add(*value, var));
                                    self.cell_values.insert(var, OptimizerValue::UnknownValue);
                                }
                            } else if let OptimizerLoopCount::NTimes(n) = iters {
                                if iters.at_least_once() {
                                    self.add_cell(var, value.wrapping_mul(n));
                                } else {
                                    self.emit(var, block);
                                    to_add.push(Instr::Add(value.wrapping_mul(n), var));
                                    self.cell_values.insert(var, OptimizerValue::UnknownValue);
                                }
                            } else if let OptimizerLoopCount::Simple = iters {
                                if iters.at_least_once() {
                                    self.add_mul_cell(var, *value, cond, block);
                                } else {
                                    self.emit(var, block);
                                    to_add.push(Instr::MulAdd(*value, cond, var));
                                    self.cell_values.insert(var, OptimizerValue::UnknownValue);
                                }
                            } else if let OptimizerLoopCount::SimpleNegated = iters {
                                if iters.at_least_once() {
                                    self.add_mul_cell(var, value.wrapping_neg(), cond, block);
                                } else {
                                    self.emit(var, block);
                                    to_add.push(Instr::MulAdd(value.wrapping_neg(), cond, var));
                                    self.cell_values.insert(var, OptimizerValue::UnknownValue);
                                }
                            } else {
                                self.emit(var, block);
                                sub_cxt.emit(var, &mut sub_block);
                            }
                        }
                    }
                }
                if sub_block.is_empty() && iters.is_finite() {
                    // This loop can be removed.
                    sub_cxt.load_cell(cond, C::ZERO);
                } else if iters.at_most_once() {
                    to_add.append(&mut sub_block);
                    sub_cxt.load_cell(cond, C::ZERO);
                } else {
                    sub_cxt.emit(cond, &mut sub_block);
                    self.emit(cond, block);
                    to_add.push(Instr::Loop(cond, sub_block))
                }
                if iters.effects_seen_later() {
                    for var in &sub_cxt.written_cells {
                        self.cell_values.insert(*var, OptimizerValue::UnknownValue);
                    }
                    for var in sub_cxt.pending() {
                        if var != cond {
                            match sub_cxt.cell_values.get(&var) {
                                Some(OptimizerValue::UnknownAddition { pending }) => {
                                    to_add.push(Instr::Add(*pending, var));
                                    self.cell_values.insert(var, OptimizerValue::UnknownValue);
                                }
                                Some(OptimizerValue::KnownValue { value, .. }) => {
                                    if iters.at_least_once() {
                                        self.load_cell(var, *value);
                                    } else {
                                        to_add.push(Instr::Load(*value, var));
                                        self.cell_values.insert(var, OptimizerValue::UnknownValue);
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
                if iters.at_least_once()
                    || to_add.is_empty()
                    || (to_add.len() == 1
                        && if let Instr::Loop(c, _) = to_add[0] {
                            c == cond
                        } else {
                            false
                        })
                {
                    block.append(&mut to_add);
                } else {
                    sub_cxt.emit(cond, &mut to_add);
                    self.emit(cond, block);
                    block.push(Instr::Loop(cond, to_add));
                }
            }
        }
        self.load_cell(cond, C::ZERO);
    }

    /// Optimize the given block. This will assume that the block is not used
    /// inside a loop. If the block is used inside a loop, some additional
    /// finalization logic is required.
    fn optimize_block(&mut self, block: Block<C>) -> Block<C> {
        let mut optimized = Block::new();
        for instr in block {
            match instr {
                Instr::Move(offset) => self.ptr += offset,
                Instr::Load(val, dst) => {
                    let dst = dst + self.ptr;
                    self.load_cell(dst, val);
                }
                Instr::Add(val, dst) => {
                    let dst = dst + self.ptr;
                    self.add_cell(dst, val);
                }
                Instr::MulAdd(val, src, dst) => {
                    let src = src + self.ptr;
                    let dst = dst + self.ptr;
                    self.add_mul_cell(dst, val, src, &mut optimized);
                }
                Instr::Output(src) => {
                    let src = src + self.ptr;
                    self.emit(src, &mut optimized);
                    optimized.push(Instr::Output(src));
                }
                Instr::Input(dst) => {
                    let dst = dst + self.ptr;
                    optimized.push(Instr::Input(dst));
                    self.cell_values.insert(dst, OptimizerValue::UnknownValue);
                    self.written_cells.insert(dst);
                }
                Instr::Loop(cond, sub_block) => {
                    let cond = cond + self.ptr;
                    self.loop_on(cond, sub_block, &mut optimized);
                }
            }
        }
        return optimized;
    }
}

/// Optimize the Brainfuck program. It should be noted that the performed
/// optimizations are very much specific to this vm and use non-brainfuck
/// instructions. This is mainly a constant propagation pass.
pub fn optimize<C: CellType>(program: Block<C>) -> Block<C> {
    return OptimizerContext::new(true, 0).optimize_block(program);
}

#[cfg(test)]
mod tests {
    use crate::{optimize, parse, Context, Error, ErrorKind, Instr};
    use Instr::*;

    #[test]
    fn parsing_valid_brainfuck_returns_block() -> Result<(), Error> {
        let prog = parse::<u8>("+++++[>[-],.<--]")?;
        assert_eq!(
            prog,
            vec![
                Add(5, 0),
                Loop(
                    0,
                    vec![
                        Move(1),
                        Loop(0, vec![Add(255, 0)]),
                        Input(0),
                        Output(0),
                        Move(-1),
                        Add(254, 0),
                    ]
                ),
            ]
        );
        Ok(())
    }

    #[test]
    fn parsing_with_missing_closing_returns_error() {
        let prog = parse::<u8>("+++++[>[-],.<--");
        assert_eq!(
            prog,
            Err(Error {
                kind: ErrorKind::LoopNotClosed,
                position: 5
            })
        );
    }

    #[test]
    fn parsing_with_missing_opening_return_error() {
        let prog = parse::<u8>("+++++>[-],.<]--");
        assert_eq!(
            prog,
            Err(Error {
                kind: ErrorKind::LoopNotOpened,
                position: 12
            })
        );
    }

    #[test]
    fn optimize_simple_program() -> Result<(), Error> {
        let prog = parse::<u8>("+++++[>[-],.<--]")?;
        let prog = optimize(prog);
        assert_eq!(
            prog,
            vec![Load(5, 0), Loop(0, vec![Input(1), Output(1), Add(254, 0),]),]
        );
        Ok(())
    }

    #[test]
    fn optimize_h() -> Result<(), Error> {
        let prog = parse::<u8>("++++++[>+++++<-]>++[>++<-]++++[>++<-]>[.>]")?;
        let prog = optimize(prog);
        let mut buf = Vec::new();
        let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
        ctx.execute(&prog);
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "H");
        Ok(())
    }

    #[test]
    fn optimize_hello_world() -> Result<(), Error> {
        let prog = parse::<u8>(
            "++++++[>+++++<-]>++[>++>+++>+++>+++>+++>+>+++>+++>++++>+++>++
            +>+<<<<<<<<<<<<-]++++[>++>+>+++>+++>+++>>-->+++>--->+++>+>>++
            <<<<<<<<<<<<<-]>>+>>>+++>>->+++>-->>>+>++<<<<<<<<<<<<<>[.>]",
        )?;
        let prog = optimize(prog);
        let mut buf = Vec::new();
        let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
        ctx.execute(&prog);
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
        Ok(())
    }

    #[test]
    fn optimize_hello_world_u8() -> Result<(), Error> {
        let prog = parse::<u8>(
            ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.",
        )?;
        let prog = optimize(prog);
        let mut buf = Vec::new();
        let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
        ctx.execute(&prog);
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
        Ok(())
    }

    #[test]
    fn optimize_hello_world_u16() -> Result<(), Error> {
        let prog = parse::<u16>(
            ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.",
        )?;
        let prog = optimize(prog);
        let mut buf = Vec::new();
        let mut ctx = Context::<u16>::new(None, Some(Box::new(&mut buf)));
        ctx.execute(&prog);
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
        Ok(())
    }

    #[test]
    fn optimize_hello_world_u32() -> Result<(), Error> {
        let prog = parse::<u32>(
            ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.",
        )?;
        eprintln!("{:?}", prog);
        let prog = optimize(prog);
        eprintln!("{:?}", prog);
        let mut buf = Vec::new();
        let mut ctx = Context::<u32>::new(None, Some(Box::new(&mut buf)));
        ctx.execute(&prog);
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
        Ok(())
    }

    #[test]
    fn optimize_hello_world_u64() -> Result<(), Error> {
        let prog = parse::<u64>(
            ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.",
        )?;
        eprintln!("{:?}", prog);
        let prog = optimize(prog);
        eprintln!("{:?}", prog);
        let mut buf = Vec::new();
        let mut ctx = Context::<u64>::new(None, Some(Box::new(&mut buf)));
        ctx.execute(&prog);
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
        Ok(())
    }

    #[test]
    fn optimize_hello_world_minimal() -> Result<(), Error> {
        let prog = parse::<u8>(
            "+[-->-[>>+>-----<<]<--<---]>-.>>>+.>>..+++[.>]<<<<.+++.------.<<-.>>>>+."
        )?;
        eprintln!("{:?}", prog);
        let prog = optimize(prog);
        eprintln!("{:?}", prog);
        let mut buf = Vec::new();
        let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
        ctx.execute(&prog);
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello, World!");
        Ok(())
    }
}
