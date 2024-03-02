use std::ptr;

use crate::{
    bc::{Instr, Loc},
    CellType,
};

use super::OpsContext;

type Op<C> = unsafe fn(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C);

pub union OpCode<C: CellType> {
    op: Op<C>,
    off: isize,
    idx: usize,
    val: C,
}

trait OpRead<C: CellType> {
    const SHIFT: usize;

    unsafe fn read(cxt: *mut OpsContext<C>, mem: *mut C, ip: *const OpCode<C>, r0: C, r1: C) -> C;
}

trait OpWrite<C: CellType>: OpRead<C> {
    unsafe fn write(
        cxt: *mut OpsContext<C>,
        mem: *mut C,
        ip: *const OpCode<C>,
        r0: C,
        r1: C,
        value: C,
    ) -> (C, C);
}

struct Mem;
struct Tmp;
struct Imm;
struct Reg0;
struct Reg1;

impl<C: CellType> OpWrite<C> for Mem {
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
    unsafe fn write(
        cxt: *mut OpsContext<C>,
        _mem: *mut C,
        ip: *const OpCode<C>,
        r0: C,
        r1: C,
        value: C,
    ) -> (C, C) {
        *(*cxt).temps.as_mut_ptr().add((*ip).idx) = value;
        (r0, r1)
    }
}

impl<C: CellType> OpWrite<C> for Reg0 {
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

impl<C: CellType> OpRead<C> for Tmp {
    const SHIFT: usize = 1;

    unsafe fn read(
        cxt: *mut OpsContext<C>,
        _mem: *mut C,
        ip: *const OpCode<C>,
        _r0: C,
        _r1: C,
    ) -> C {
        *(*cxt).temps.as_mut_ptr().add((*ip).idx)
    }
}

impl<C: CellType> OpRead<C> for Imm {
    const SHIFT: usize = 1;

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

#[cfg(debug_assertions)]
unsafe fn noop<C: CellType>(
    _cxt: *mut OpsContext<C>,
    _mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    (ip.add(1), r0, r1)
}

#[cfg(not(debug_assertions))]
unsafe fn noop<C: CellType>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    mut ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    ip = ip.add(1);
    ((*ip).op)(cxt, mem, ip, r0, r1)
}

unsafe fn scanl<C: CellType>(
    cxt: *mut OpsContext<C>,
    mut mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    let cond = (*ip.add(1)).off;
    let shift = (*ip.add(2)).off;
    while *mem.offset(cond) != C::ZERO {
        (*cxt).context.memory.mov(shift);
        if !(*cxt).context.memory.check((*cxt).min_accessed) {
            (*cxt)
                .context
                .memory
                .make_accessible((*cxt).min_accessed, (*cxt).max_accessed + 1);
        }
        mem = (*cxt).context.memory.current_ptr();
    }
    noop(cxt, mem, ip.add(2), r0, r1)
}

unsafe fn scanr<C: CellType>(
    cxt: *mut OpsContext<C>,
    mut mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    let cond = (*ip.add(1)).off;
    let shift = (*ip.add(2)).off;
    while *mem.offset(cond) != C::ZERO {
        (*cxt).context.memory.mov(shift);
        if !(*cxt).context.memory.check((*cxt).max_accessed) {
            (*cxt)
                .context
                .memory
                .make_accessible((*cxt).min_accessed, (*cxt).max_accessed + 1);
        }
        mem = (*cxt).context.memory.current_ptr();
    }
    noop(cxt, mem, ip.add(2), r0, r1)
}

unsafe fn movl<C: CellType>(
    cxt: *mut OpsContext<C>,
    _mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    let shift = (*ip.add(1)).off;
    (*cxt).context.memory.mov(shift);
    if !(*cxt).context.memory.check((*cxt).min_accessed) {
        (*cxt)
            .context
            .memory
            .make_accessible((*cxt).min_accessed, (*cxt).max_accessed + 1);
    }
    noop(cxt, (*cxt).context.memory.current_ptr(), ip.add(1), r0, r1)
}

unsafe fn movr<C: CellType>(
    cxt: *mut OpsContext<C>,
    _mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    let shift = (*ip.add(1)).off;
    (*cxt).context.memory.mov(shift);
    if !(*cxt).context.memory.check((*cxt).max_accessed) {
        (*cxt)
            .context
            .memory
            .make_accessible((*cxt).min_accessed, (*cxt).max_accessed + 1);
    }
    noop(cxt, (*cxt).context.memory.current_ptr(), ip.add(1), r0, r1)
}

unsafe fn input<C: CellType>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    let dst = (*ip.add(1)).off;
    if let Some(inp) = (*cxt).context.input() {
        let val = C::from_u8(inp);
        *mem.offset(dst) = val;
        noop(cxt, mem, ip.add(1), r0, r1)
    } else {
        (ptr::null(), r0, r1)
    }
}

unsafe fn output<C: CellType>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    let src = (*ip.add(1)).off;
    let val = *mem.offset(src);
    if let Some(()) = (*cxt).context.output(val.into_u8()) {
        noop(cxt, mem, ip.add(1), r0, r1)
    } else {
        (ptr::null(), r0, r1)
    }
}

unsafe fn brz<C: CellType>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    let cond = (*ip.add(1)).off;
    let off = (*ip.add(2)).off;
    if *mem.offset(cond) == C::ZERO {
        noop(cxt, mem, ip.offset(off - 1), r0, r1)
    } else {
        noop(cxt, mem, ip.add(2), r0, r1)
    }
}

unsafe fn brnz<C: CellType>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    let cond = (*ip.add(1)).off;
    let off = (*ip.add(2)).off;
    if *mem.offset(cond) != C::ZERO {
        noop(cxt, mem, ip.offset(off - 1), r0, r1)
    } else {
        noop(cxt, mem, ip.add(2), r0, r1)
    }
}

unsafe fn add<C: CellType, Dst: OpWrite<C>, Src: OpRead<C>>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    mut ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    ip = ip.add(Src::SHIFT);
    let val0 = Src::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Dst::SHIFT);
    let val1 = Dst::read(cxt, mem, ip, r0, r1);
    Dst::write(cxt, mem, ip, r0, r1, val0.wrapping_add(val1));
    noop(cxt, mem, ip, r0, r1)
}

unsafe fn add2<C: CellType, Dst: OpWrite<C>, Src0: OpRead<C>, Src1: OpRead<C>>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    mut ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    ip = ip.add(Src0::SHIFT);
    let val0 = Src0::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Src1::SHIFT);
    let val1 = Src1::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Dst::SHIFT);
    Dst::write(cxt, mem, ip, r0, r1, val0.wrapping_add(val1));
    noop(cxt, mem, ip, r0, r1)
}

unsafe fn sub<C: CellType, Dst: OpWrite<C>, Src: OpRead<C>>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    mut ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    ip = ip.add(Src::SHIFT);
    let val0 = Src::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Dst::SHIFT);
    let val1 = Dst::read(cxt, mem, ip, r0, r1);
    Dst::write(cxt, mem, ip, r0, r1, val1.wrapping_add(val0.wrapping_neg()));
    noop(cxt, mem, ip, r0, r1)
}

unsafe fn sub2<C: CellType, Dst: OpWrite<C>, Src0: OpRead<C>, Src1: OpRead<C>>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    mut ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    ip = ip.add(Src0::SHIFT);
    let val0 = Src0::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Src1::SHIFT);
    let val1 = Src1::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Dst::SHIFT);
    Dst::write(cxt, mem, ip, r0, r1, val0.wrapping_add(val1.wrapping_neg()));
    noop(cxt, mem, ip, r0, r1)
}

unsafe fn mul<C: CellType, Dst: OpWrite<C>, Src: OpRead<C>>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    mut ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    ip = ip.add(Src::SHIFT);
    let val0 = Src::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Dst::SHIFT);
    let val1 = Dst::read(cxt, mem, ip, r0, r1);
    Dst::write(cxt, mem, ip, r0, r1, val0.wrapping_mul(val1));
    noop(cxt, mem, ip, r0, r1)
}

unsafe fn mul2<C: CellType, Dst: OpWrite<C>, Src0: OpRead<C>, Src1: OpRead<C>>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    mut ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    ip = ip.add(Src0::SHIFT);
    let val0 = Src0::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Src1::SHIFT);
    let val1 = Src1::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Dst::SHIFT);
    Dst::write(cxt, mem, ip, r0, r1, val0.wrapping_mul(val1));
    noop(cxt, mem, ip, r0, r1)
}

unsafe fn copy<C: CellType, Dst: OpWrite<C>, Src: OpRead<C>>(
    cxt: *mut OpsContext<C>,
    mem: *mut C,
    mut ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    ip = ip.add(Src::SHIFT);
    let val = Src::read(cxt, mem, ip, r0, r1);
    ip = ip.add(Dst::SHIFT);
    Dst::write(cxt, mem, ip, r0, r1, val);
    noop(cxt, mem, ip, r0, r1)
}

unsafe fn ret<C: CellType>(
    _cxt: *mut OpsContext<C>,
    _mem: *mut C,
    _ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    (ptr::null(), r0, r1)
}

pub unsafe fn enter_ops<C: CellType>(
    cxt: *mut OpsContext<C>,
    _mem: *mut C,
    ip: *const OpCode<C>,
    r0: C,
    r1: C,
) -> (*const OpCode<C>, C, C) {
    (*cxt)
        .context
        .memory
        .make_accessible((*cxt).min_accessed, (*cxt).max_accessed + 1);
    ((*ip).op)(cxt, (*cxt).context.memory.current_ptr(), ip, r0, r1)
}

pub fn emit_return<C: CellType>(insts: &mut Vec<OpCode<C>>) {
    insts.push(OpCode { op: ret });
}

/// Some macro black magic that creates an `if let` for every possible combination
/// of source and target operands. Let's hope the compiler optimizes this somehow.
/// However, this has a very negative effect on compile times.
macro_rules! op_match {
    (@loop $insts:ident, $inst:ident, $instr:path, $op:ident, , [$($match:tt)*], [$($gen:tt)*], [$($push:tt)*]) => (
        if let $instr(Loc::Tmp(0), $($match)*) = $inst {
            $insts.push(OpCode { op: $op::<_, Reg0, $($gen)*>, });
            $($push)*
            return;
        }
        if let $instr(Loc::Tmp(1), $($match)*) = $inst {
            $insts.push(OpCode { op: $op::<_, Reg1, $($gen)*>, });
            $($push)*
            return;
        }
        if let $instr(Loc::Tmp(idx), $($match)*) = $inst {
            $insts.push(OpCode { op: $op::<_, Tmp, $($gen)*>, });
            $($push)*
            $insts.push(OpCode { idx });
            return;
        }
        if let $instr(Loc::Mem(off), $($match)*) = $inst {
            $insts.push(OpCode { op: $op::<_, Mem, $($gen)*>, });
            $($push)*
            $insts.push(OpCode { off });
            return;
        }
    );
    (@loop $insts:ident, $inst:ident, $instr:path, $op:ident, w, [$($match:tt)*], [$($gen:tt)*], [$($push:tt)*]) => (
        if let $instr(Loc::Tmp(0), Loc::Tmp(0), $($match)*) = $inst {
            $insts.push(OpCode { op: $op::<_, Reg0, $($gen)*>, });
            $($push)*
            return;
        }
        if let $instr(Loc::Tmp(1), Loc::Tmp(1), $($match)*) = $inst {
            $insts.push(OpCode { op: $op::<_, Reg1, $($gen)*>, });
            $($push)*
            return;
        }
        if let $instr(Loc::Tmp(idx), Loc::Tmp(idx2), $($match)*) = $inst {
            if idx == idx2 {
                $insts.push(OpCode { op: $op::<_, Tmp, $($gen)*>, });
                $($push)*
                $insts.push(OpCode { idx });
                return;
            }
        }
        if let $instr(Loc::Mem(off), Loc::Mem(off2), $($match)*) = $inst {
            if off == off2 {
                $insts.push(OpCode { op: $op::<_, Mem, $($gen)*>, });
                $($push)*
                $insts.push(OpCode { off });
                return;
            }
        }
    );
    (@loop $insts:ident, $inst:ident, $instr:path, $op:ident, r $($r:ident)*, [$($match:tt)*], [$($gen:tt)*], [$($push:tt)*]) => (
        op_match!(
            @loop $insts, $inst, $instr, $op, $($r)*,
            [Loc::Tmp(0), $($match)*], [Reg0, $($gen)*], [$($push)*]
        );
        op_match!(
            @loop $insts, $inst, $instr, $op, $($r)*,
            [Loc::Tmp(1), $($match)*], [Reg1, $($gen)*], [$($push)*]
        );
        op_match!(
            @loop $insts, $inst, $instr, $op, $($r)*,
            [Loc::Tmp(idx), $($match)*], [Tmp, $($gen)*], [$insts.push(OpCode { idx }); $($push)*]
        );
        op_match!(
            @loop $insts, $inst, $instr, $op, $($r)*,
            [Loc::Mem(off), $($match)*], [Mem, $($gen)*], [$insts.push(OpCode { off }); $($push)*]
        );
        op_match!(
            @loop $insts, $inst, $instr, $op, $($r)*,
            [Loc::Imm(val), $($match)*], [Imm, $($gen)*], [$insts.push(OpCode { val }); $($push)*]
        );
    );
    ($insts:ident, $inst:ident, $instr:path, $op:ident, $($r:ident)*) => (
        op_match!(@loop $insts, $inst, $instr, $op, $($r)*, [], [], []);
    );
}

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
        Instr::BrZ(cond, off) => {
            insts.push(OpCode { op: brz });
            insts.push(OpCode { off: cond });
            insts.push(OpCode { off });
        }
        Instr::BrNZ(cond, off) => {
            insts.push(OpCode { op: brnz });
            insts.push(OpCode { off: cond });
            insts.push(OpCode { off });
        }
        _ => unimplemented!("bytecode instruction `{instr:?}`"),
    }
}

pub fn adjust_branch<C: CellType>(branch_instr: &mut [OpCode<C>], offset: isize) {
    branch_instr[2].off = offset;
}
