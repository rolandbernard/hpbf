//! Operations of the threaded code instruction stream.

use std::ptr;

use crate::{
    bc::{Instr, Loc},
    CellType,
};

use super::OpsContext;

/// The signature of the threaded code segments.
type Op<C> = unsafe fn(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> *const OpCode<C>;

/// An element in the instruction stream for the threaded code.
pub union OpCode<C: CellType> {
    op: Op<C>,
    off: isize,
    idx: usize,
    val: C,
}

/// Trait for reading a value from some location in the virtual machine.
trait OpRead<C: CellType> {
    /// The number of instruction stream items consumed by a read.
    const SHIFT: usize;

    /// Read the value and return it.
    unsafe fn read(cxt: *mut OpsContext<C>, mem: *mut C, ip: *const OpCode<C>, r0: C, r1: C) -> C;
}

/// Trait for writing a value to some location in the virtual machine.
trait OpWrite<C: CellType>: OpRead<C> {
    /// Write the given `value` and return the new state of the registers.
    unsafe fn write(
        cxt: *mut OpsContext<C>,
        mem: *mut C,
        ip: *const OpCode<C>,
        r0: C,
        r1: C,
        value: C,
    ) -> (C, C);
}

/// Read/write from a memory location. The offset is passed in the instruction stream.
struct Mem;

/// Read from a memory location and zero it. The offset is passed in the instruction stream.
struct MemZero;

/// Read/write from a temporary. The index is passed in the instruction stream.
struct Tmp;

/// Read an immediate value from the instruction stream.
struct Imm;

/// Read/write to the first register.
struct Reg0;

/// Read/write to the second register.
struct Reg1;

/// Read constant zero.
struct Zero;

/// Read constant one.
struct One;

/// Read constant negative one.
struct NegOne;

unsafe fn temps_ptr<C: CellType>(cxt: *mut OpsContext<C>) -> *mut C {
    ptr::addr_of_mut!((*cxt).temps) as *mut _
}

impl<C: CellType> OpWrite<C> for Mem {
    #[inline(always)]
    unsafe fn write(
        _cxt: *mut OpsContext<C>,
        mem: *mut C,
        ip: *const OpCode<C>,
        r0: C,
        r1: C,
        value: C,
    ) -> (C, C) {
        *mem.offset((*ip).off) = value;
        (r0, r1)
    }
}

impl<C: CellType> OpWrite<C> for Tmp {
    #[inline(always)]
    unsafe fn write(
        cxt: *mut OpsContext<C>,
        _mem: *mut C,
        ip: *const OpCode<C>,
        r0: C,
        r1: C,
        value: C,
    ) -> (C, C) {
        *temps_ptr(cxt).add((*ip).idx) = value;
        (r0, r1)
    }
}

impl<C: CellType> OpWrite<C> for Reg0 {
    #[inline(always)]
    unsafe fn write(
        _cxt: *mut OpsContext<C>,
        _mem: *mut C,
        _ip: *const OpCode<C>,
        _r0: C,
        r1: C,
        value: C,
    ) -> (C, C) {
        (value, r1)
    }
}

impl<C: CellType> OpWrite<C> for Reg1 {
    #[inline(always)]
    unsafe fn write(
        _cxt: *mut OpsContext<C>,
        _mem: *mut C,
        _ip: *const OpCode<C>,
        r0: C,
        _r1: C,
        value: C,
    ) -> (C, C) {
        (r0, value)
    }
}

impl<C: CellType> OpRead<C> for Mem {
    const SHIFT: usize = 1;

    #[inline(always)]
    unsafe fn read(
        _cxt: *mut OpsContext<C>,
        mem: *mut C,
        ip: *const OpCode<C>,
        _r0: C,
        _r1: C,
    ) -> C {
        *mem.offset((*ip).off)
    }
}

impl<C: CellType> OpRead<C> for MemZero {
    const SHIFT: usize = 1;

    #[inline(always)]
    unsafe fn read(
        _cxt: *mut OpsContext<C>,
        mem: *mut C,
        ip: *const OpCode<C>,
        _r0: C,
        _r1: C,
    ) -> C {
        let off = (*ip).off;
        let result = *mem.offset(off);
        *mem.offset(off) = C::ZERO;
        result
    }
}

impl<C: CellType> OpRead<C> for Tmp {
    const SHIFT: usize = 1;

    #[inline(always)]
    unsafe fn read(
        cxt: *mut OpsContext<C>,
        _mem: *mut C,
        ip: *const OpCode<C>,
        _r0: C,
        _r1: C,
    ) -> C {
        *temps_ptr(cxt).add((*ip).idx)
    }
}

impl<C: CellType> OpRead<C> for Imm {
    const SHIFT: usize = 1;

    #[inline(always)]
    unsafe fn read(
        _cxt: *mut OpsContext<C>,
        _mem: *mut C,
        ip: *const OpCode<C>,
        _r0: C,
        _r1: C,
    ) -> C {
        (*ip).val
    }
}

impl<C: CellType> OpRead<C> for Reg0 {
    const SHIFT: usize = 0;

    #[inline(always)]
    unsafe fn read(
        _cxt: *mut OpsContext<C>,
        _mem: *mut C,
        _ip: *const OpCode<C>,
        r0: C,
        _r1: C,
    ) -> C {
        r0
    }
}

impl<C: CellType> OpRead<C> for Reg1 {
    const SHIFT: usize = 0;

    #[inline(always)]
    unsafe fn read(
        _cxt: *mut OpsContext<C>,
        _mem: *mut C,
        _ip: *const OpCode<C>,
        _r0: C,
        r1: C,
    ) -> C {
        r1
    }
}

impl<C: CellType> OpRead<C> for Zero {
    const SHIFT: usize = 0;

    #[inline(always)]
    unsafe fn read(
        _cxt: *mut OpsContext<C>,
        _mem: *mut C,
        _ip: *const OpCode<C>,
        _r0: C,
        _r1: C,
    ) -> C {
        C::ZERO
    }
}

impl<C: CellType> OpRead<C> for One {
    const SHIFT: usize = 0;

    #[inline(always)]
    unsafe fn read(
        _cxt: *mut OpsContext<C>,
        _mem: *mut C,
        _ip: *const OpCode<C>,
        _r0: C,
        _r1: C,
    ) -> C {
        C::ONE
    }
}

impl<C: CellType> OpRead<C> for NegOne {
    const SHIFT: usize = 0;

    #[inline(always)]
    unsafe fn read(
        _cxt: *mut OpsContext<C>,
        _mem: *mut C,
        _ip: *const OpCode<C>,
        _r0: C,
        _r1: C,
    ) -> C {
        C::NEG_ONE
    }
}

/// Noop instruction that does not change the virtual machine state. In debug mode,
/// this operation return immediately with the address of the next instruction.
#[cfg(debug_assertions)]
unsafe fn noop<C: CellType>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> *const OpCode<C> {
    temps_ptr(cxt).add(0).write(r0);
    temps_ptr(cxt).add(1).write(r1);
    (*cxt).context.memory.set_current_ptr(mem);
    ip.add(1)
}

/// Noop instruction that does not change the virtual machine state. In release mode,
/// this operation will directly call the next instruction. This assumes that there
/// will be tail call optimizations applied to avoid stack overflow.
#[cfg(not(debug_assertions))]
#[inline(always)]
unsafe fn noop<C: CellType>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    mut ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> *const OpCode<C> {
    ip = ip.add(1);
    ((*ip).op)(cxt, mem, ip, r0, r1)
}

/// Check that the given memory location does not need a resize. If a resize is
/// needed, it is performed and the new memory pointer returned. This will only
/// check the lower memory limit.
#[inline(always)]
unsafe fn checkl<C: CellType>(cxt: *mut OpsContext<C>, mem: *mut C) -> *mut C {
    if !(*cxt)
        .context
        .memory
        .check_ptr(mem.wrapping_offset((*cxt).min_accessed))
    {
        (*cxt).context.memory.set_current_ptr(mem);
        (*cxt)
            .context
            .memory
            .make_accessible((*cxt).min_accessed, (*cxt).max_accessed + 1);
        (*cxt).context.memory.current_ptr()
    } else {
        mem
    }
}

/// Check that the given memory location does not need a resize. If a resize is
/// needed, it is performed and the new memory pointer returned. This will only
/// check the upper memory limit.
#[inline(always)]
unsafe fn checkr<C: CellType>(cxt: *mut OpsContext<C>, mem: *mut C) -> *mut C {
    if !(*cxt)
        .context
        .memory
        .check_ptr(mem.wrapping_offset((*cxt).max_accessed))
    {
        (*cxt).context.memory.set_current_ptr(mem);
        (*cxt)
            .context
            .memory
            .make_accessible((*cxt).min_accessed, (*cxt).max_accessed + 1);
        (*cxt).context.memory.current_ptr()
    } else {
        mem
    }
}

/// Move the memory pointer to the left until the condition is false.
unsafe fn scanl<C: CellType>(
    cxt: *mut OpsContext<C>,
    mut mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> *const OpCode<C> {
    let cond = (*ip.add(1)).off;
    let shift = (*ip.add(2)).off;
    while *mem.offset(cond) != C::ZERO {
        mem = checkl(cxt, mem.wrapping_offset(shift));
    }
    noop(cxt, mem, ip.add(2), r0, r1)
}

/// Move the memory pointer to the right until the condition is false.
unsafe fn scanr<C: CellType>(
    cxt: *mut OpsContext<C>,
    mut mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> *const OpCode<C> {
    let cond = (*ip.add(1)).off;
    let shift = (*ip.add(2)).off;
    while *mem.offset(cond) != C::ZERO {
        mem = checkr(cxt, mem.wrapping_offset(shift));
    }
    noop(cxt, mem, ip.add(2), r0, r1)
}

/// Move the memory pointer to the left and perform bounds checks.
unsafe fn movl<C: CellType>(
    cxt: *mut OpsContext<C>,
    mut mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> *const OpCode<C> {
    let shift = (*ip.add(1)).off;
    mem = checkl(cxt, mem.wrapping_offset(shift));
    noop(cxt, mem, ip.add(1), r0, r1)
}

/// Move the memory pointer to the right and perform bounds checks.
unsafe fn movr<C: CellType>(
    cxt: *mut OpsContext<C>,
    mut mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> *const OpCode<C> {
    let shift = (*ip.add(1)).off;
    mem = checkr(cxt, mem.wrapping_offset(shift));
    noop(cxt, mem, ip.add(1), r0, r1)
}

/// Input from the input stream and save the value at a given memory location.
unsafe fn input<C: CellType>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> *const OpCode<C> {
    if let Some(inp) = (*cxt).context.input() {
        let val = C::from_u8(inp);
        let dst = (*ip.add(1)).off;
        *mem.offset(dst) = val;
        noop(cxt, mem, ip.add(1), r0, r1)
    } else {
        ptr::null()
    }
}

/// Output the value at given memory location to the output stream.
unsafe fn output<C: CellType>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> *const OpCode<C> {
    let src = (*ip.add(1)).off;
    let val = *mem.offset(src);
    if let Some(()) = (*cxt).context.output(val.into_u8()) {
        noop(cxt, mem, ip.add(1), r0, r1)
    } else {
        ptr::null()
    }
}

/// Branch if a given condition is zero. Instead of running the next instruction
/// move the instruction pointer by an offset given in the instruction stream.
unsafe fn brz<C: CellType>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> *const OpCode<C> {
    let cond = (*ip.add(1)).off;
    if *mem.offset(cond) == C::ZERO {
        let off = (*ip.add(2)).off;
        noop(cxt, mem, ip.offset(off - 1), r0, r1)
    } else {
        noop(cxt, mem, ip.add(2), r0, r1)
    }
}

/// Branch if a given condition is not zero. Instead of running the next instruction
/// move the instruction pointer by an offset given in the instruction stream.
unsafe fn brnz<C: CellType>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> *const OpCode<C> {
    let cond = (*ip.add(1)).off;
    if *mem.offset(cond) != C::ZERO {
        let off = (*ip.add(2)).off;
        noop(cxt, mem, ip.offset(off - 1), r0, r1)
    } else {
        noop(cxt, mem, ip.add(2), r0, r1)
    }
}

/// Store the result of adding `Dst` and `Src` into `Dst`.
unsafe fn add<C: CellType, Dst: OpWrite<C>, Src: OpRead<C>>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    mut ip: *const OpCode<C>,
    mut r0: C,
    mut r1: C,
) -> *const OpCode<C> {
    ip = ip.add(Src::SHIFT);
    let val0 = Src::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Dst::SHIFT);
    let val1 = Dst::read(cxt, mem, ip, r0, r1);
    (r0, r1) = Dst::write(cxt, mem, ip, r0, r1, val0.wrapping_add(val1));
    noop(cxt, mem, ip, r0, r1)
}

/// Store the result of adding `Src0` and `Src1` into `Dst`.
unsafe fn add2<C: CellType, Dst: OpWrite<C>, Src0: OpRead<C>, Src1: OpRead<C>>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    mut ip: *const OpCode<C>,
    mut r0: C,
    mut r1: C,
) -> *const OpCode<C> {
    ip = ip.add(Src0::SHIFT);
    let val0 = Src0::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Src1::SHIFT);
    let val1 = Src1::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Dst::SHIFT);
    (r0, r1) = Dst::write(cxt, mem, ip, r0, r1, val0.wrapping_add(val1));
    noop(cxt, mem, ip, r0, r1)
}

/// Store the result of subtracting `Src` from `Dst` into `Dst`.
unsafe fn sub<C: CellType, Dst: OpWrite<C>, Src: OpRead<C>>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    mut ip: *const OpCode<C>,
    mut r0: C,
    mut r1: C,
) -> *const OpCode<C> {
    ip = ip.add(Src::SHIFT);
    let val0 = Src::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Dst::SHIFT);
    let val1 = Dst::read(cxt, mem, ip, r0, r1);
    (r0, r1) = Dst::write(cxt, mem, ip, r0, r1, val1.wrapping_add(val0.wrapping_neg()));
    noop(cxt, mem, ip, r0, r1)
}

/// Store the result of subtracting `Src1` from `Src0` into `Dst`.
unsafe fn sub2<C: CellType, Dst: OpWrite<C>, Src0: OpRead<C>, Src1: OpRead<C>>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    mut ip: *const OpCode<C>,
    mut r0: C,
    mut r1: C,
) -> *const OpCode<C> {
    ip = ip.add(Src0::SHIFT);
    let val0 = Src0::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Src1::SHIFT);
    let val1 = Src1::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Dst::SHIFT);
    (r0, r1) = Dst::write(cxt, mem, ip, r0, r1, val0.wrapping_add(val1.wrapping_neg()));
    noop(cxt, mem, ip, r0, r1)
}

/// Store the result of multiplying `Dst` and `Src` into `Dst`.
unsafe fn mul<C: CellType, Dst: OpWrite<C>, Src: OpRead<C>>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    mut ip: *const OpCode<C>,
    mut r0: C,
    mut r1: C,
) -> *const OpCode<C> {
    ip = ip.add(Src::SHIFT);
    let val0 = Src::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Dst::SHIFT);
    let val1 = Dst::read(cxt, mem, ip, r0, r1);
    (r0, r1) = Dst::write(cxt, mem, ip, r0, r1, val0.wrapping_mul(val1));
    noop(cxt, mem, ip, r0, r1)
}

/// Store the result of multiplying `Src0` and `Src1` into `Dst`.
unsafe fn mul2<C: CellType, Dst: OpWrite<C>, Src0: OpRead<C>, Src1: OpRead<C>>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    mut ip: *const OpCode<C>,
    mut r0: C,
    mut r1: C,
) -> *const OpCode<C> {
    ip = ip.add(Src0::SHIFT);
    let val0 = Src0::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Src1::SHIFT);
    let val1 = Src1::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Dst::SHIFT);
    (r0, r1) = Dst::write(cxt, mem, ip, r0, r1, val0.wrapping_mul(val1));
    noop(cxt, mem, ip, r0, r1)
}

/// Store the value of `Src` into `Dst`.
unsafe fn copy<C: CellType, Dst: OpWrite<C>, Src: OpRead<C>>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    mut ip: *const OpCode<C>,
    mut r0: C,
    mut r1: C,
) -> *const OpCode<C> {
    ip = ip.add(Src::SHIFT);
    let val = Src::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Dst::SHIFT);
    (r0, r1) = Dst::write(cxt, mem, ip, r0, r1, val);
    noop(cxt, mem, ip, r0, r1)
}

/// Immediately return the program. This returns a null pointer to indicate the
/// end of the program, as opposed to returning an instruction pointer to continue at.
unsafe fn ret<C: CellType>(
    _cxt: *mut OpsContext<C>,
    _mem: *mut C,
    _ip: *const OpCode<C>,
    _r0: C,
    _r1: C,
) -> *const OpCode<C> {
    ptr::null()
}

/// Check whether there is enough budget left to continue. If not, return.
unsafe fn limit<C: CellType>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> *const OpCode<C> {
    let cost = (*ip.add(1)).idx;
    if (*cxt).context.budget <= cost {
        (*cxt).context.budget = 0;
        temps_ptr(cxt).add(0).write(r0);
        temps_ptr(cxt).add(1).write(r1);
        (*cxt).context.memory.set_current_ptr(mem);
        ip.add(2)
    } else {
        (*cxt).context.budget -= cost;
        noop(cxt, mem, ip.add(1), r0, r1)
    }
}

/// Enter the virtual machine with the given instruction stream pointer and context.
///
/// # Safety
/// Calling this function with invalid instruction stream or context pointer will
/// cause undefined behavior. This means, e.g., all branch targets must point to
/// valid instructions, all instructions except [`ret`] must be followed by another
/// valid instruction, all memory accessed must be withing the bounds indicated in
/// `cxt`, all temporary accesses must be withing the allocation of `cxt`, etc.
pub unsafe fn enter_ops<C: CellType>(
    cxt: *mut OpsContext<C>,
    ip: *const OpCode<C>,
) -> *const OpCode<C> {
    (*cxt)
        .context
        .memory
        .make_accessible((*cxt).min_accessed, (*cxt).max_accessed + 1);
    let r0 = *temps_ptr(cxt).add(0);
    let r1 = *temps_ptr(cxt).add(1);
    let mem = (*cxt).context.memory.current_ptr();
    ((*ip).op)(cxt, mem, ip, r0, r1)
}

/// Emit a budget check instruction into `insts`.
pub fn emit_limit<C: CellType>(insts: &mut Vec<OpCode<C>>, cost: usize) {
    insts.push(OpCode { op: limit });
    insts.push(OpCode { idx: cost });
}

/// Emit a return instruction into `insts`.
pub fn emit_return<C: CellType>(insts: &mut Vec<OpCode<C>>) {
    insts.push(OpCode { op: ret });
}

/// Some macro black magic that creates an `if let` for every possible combination
/// of source and target operands. Let's hope the compiler optimizes this somehow.
/// However, this has a very negative effect on compile times.
macro_rules! op_match {
    (@loop $insts:ident, $inst:ident, $instr:path, $op:ident, , [$($match:tt)*], [$($cond:tt)*], [$($gen:tt)*], [$($push:tt)*]) => (
        if let $instr(Loc::Tmp(0), $($match)*) = $inst {
            if $($cond)* {
                $insts.push(OpCode { op: $op::<_, Reg0, $($gen)*>, });
                $($push)*
                return;
            }
        }
        if let $instr(Loc::Tmp(1), $($match)*) = $inst {
            if $($cond)* {
                $insts.push(OpCode { op: $op::<_, Reg1, $($gen)*>, });
                $($push)*
                return;
            }
        }
        if let $instr(Loc::Tmp(idx), $($match)*) = $inst {
            if $($cond)* {
                $insts.push(OpCode { op: $op::<_, Tmp, $($gen)*>, });
                $($push)*
                $insts.push(OpCode { idx });
                return;
            }
        }
        if let $instr(Loc::Mem(off), $($match)*) = $inst {
            if $($cond)* {
                $insts.push(OpCode { op: $op::<_, Mem, $($gen)*>, });
                $($push)*
                $insts.push(OpCode { off });
                return;
            }
        }
    );
    (@loop $insts:ident, $inst:ident, $instr:path, $op:ident, w, [$($match:tt)*], [$($cond:tt)*], [$($gen:tt)*], [$($push:tt)*]) => (
        if let $instr(Loc::Tmp(0), Loc::Tmp(0), $($match)*) = $inst {
            if $($cond)* {
                $insts.push(OpCode { op: $op::<_, Reg0, $($gen)*>, });
                $($push)*
                return;
            }
        }
        if let $instr(Loc::Tmp(1), Loc::Tmp(1), $($match)*) = $inst {
            if $($cond)* {
                $insts.push(OpCode { op: $op::<_, Reg1, $($gen)*>, });
                $($push)*
                return;
            }
        }
        if let $instr(Loc::Tmp(idx), Loc::Tmp(idx2), $($match)*) = $inst {
            if idx == idx2 && $($cond)* {
                $insts.push(OpCode { op: $op::<_, Tmp, $($gen)*>, });
                $($push)*
                $insts.push(OpCode { idx });
                return;
            }
        }
        if let $instr(Loc::Mem(off), Loc::Mem(off2), $($match)*) = $inst {
            if off == off2 && $($cond)* {
                $insts.push(OpCode { op: $op::<_, Mem, $($gen)*>, });
                $($push)*
                $insts.push(OpCode { off });
                return;
            }
        }
    );
    (@loop $insts:ident, $inst:ident, $instr:path, $op:ident, r $($r:ident)*, [$($match:tt)*], [$($cond:tt)*], [$($gen:tt)*], [$($push:tt)*]) => (
        op_match!(
            @loop $insts, $inst, $instr, $op, $($r)*,
            [Loc::Tmp(0), $($match)*], [$($cond)*], [Reg0, $($gen)*], [$($push)*]
        );
        op_match!(
            @loop $insts, $inst, $instr, $op, $($r)*,
            [Loc::Tmp(1), $($match)*], [$($cond)*], [Reg1, $($gen)*], [$($push)*]
        );
        op_match!(
            @loop $insts, $inst, $instr, $op, $($r)*,
            [Loc::Tmp(idx), $($match)*], [$($cond)*], [Tmp, $($gen)*], [$insts.push(OpCode { idx }); $($push)*]
        );
        op_match!(
            @loop $insts, $inst, $instr, $op, $($r)*,
            [Loc::Mem(off), $($match)*], [$($cond)*], [Mem, $($gen)*], [$insts.push(OpCode { off }); $($push)*]
        );
        op_match!(
            @loop $insts, $inst, $instr, $op, $($r)*,
            [Loc::MemZero(off), $($match)*], [$($cond)*], [MemZero, $($gen)*], [$insts.push(OpCode { off }); $($push)*]
        );
        op_match!(
            @loop $insts, $inst, $instr, $op, $($r)*,
            [Loc::Imm(val), $($match)*], [val == C::ZERO && $($cond)*], [Zero, $($gen)*], [$($push)*]
        );
        op_match!(
            @loop $insts, $inst, $instr, $op, $($r)*,
            [Loc::Imm(val), $($match)*], [val == C::ONE && $($cond)*], [One, $($gen)*], [$($push)*]
        );
        op_match!(
            @loop $insts, $inst, $instr, $op, $($r)*,
            [Loc::Imm(val), $($match)*], [val == C::NEG_ONE && $($cond)*], [NegOne, $($gen)*], [$($push)*]
        );
        op_match!(
            @loop $insts, $inst, $instr, $op, $($r)*,
            [Loc::Imm(val), $($match)*], [$($cond)*], [Imm, $($gen)*], [$insts.push(OpCode { val }); $($push)*]
        );
    );
    ($insts:ident, $inst:ident, $instr:path, $op:ident, $($r:ident)*) => (
        op_match!(@loop $insts, $inst, $instr, $op, $($r)*, [], [true], [], []);
    );
}

/// Emit a bytecode instruction into `insts`.
pub fn emit<C: CellType>(insts: &mut Vec<OpCode<C>>, instr: Instr<C>) {
    op_match!(insts, instr, Instr::Copy, copy, r);
    op_match!(insts, instr, Instr::Add, add, r w);
    op_match!(insts, instr, Instr::Add, add2, r r);
    op_match!(insts, instr, Instr::Sub, sub, r w);
    op_match!(insts, instr, Instr::Sub, sub2, r r);
    op_match!(insts, instr, Instr::Mul, mul, r w);
    op_match!(insts, instr, Instr::Mul, mul2, r r);
    match instr {
        Instr::Noop => {
            insts.push(OpCode { op: noop });
        }
        Instr::Scan(cond, shift) => {
            if shift < 0 {
                insts.push(OpCode { op: scanl });
            } else {
                insts.push(OpCode { op: scanr });
            }
            insts.push(OpCode { off: cond });
            insts.push(OpCode { off: shift });
        }
        Instr::Mov(shift) => {
            if shift < 0 {
                insts.push(OpCode { op: movl });
            } else {
                insts.push(OpCode { op: movr });
            }
            insts.push(OpCode { off: shift });
        }
        Instr::Inp(dst) => {
            insts.push(OpCode { op: input });
            insts.push(OpCode { off: dst });
        }
        Instr::Out(src) => {
            insts.push(OpCode { op: output });
            insts.push(OpCode { off: src });
        }
        Instr::BrZ(cond, _) => {
            insts.push(OpCode { op: brz });
            insts.push(OpCode { off: cond });
            insts.push(OpCode { off: 0 });
        }
        Instr::BrNZ(cond, _) => {
            insts.push(OpCode { op: brnz });
            insts.push(OpCode { off: cond });
            insts.push(OpCode { off: 0 });
        }
        _ => unimplemented!("bytecode instruction `{instr:?}`"),
    }
}

/// Adjust a target of a branch. Note that doing this for a non-branch location
/// or specifying an offset to an invalid location, will make a later call to
/// [`enter_ops`] undefined behavior.
pub fn adjust_branch<C: CellType>(branch_instr: &mut [OpCode<C>], offset: isize) {
    branch_instr[2].off = offset;
}
