//! This module contains code generation specific to this implementation. It uses
//! the definitions in [`super::asm`] to emit machine code and does relocation
//! based on the assumption that the pc relative address is in the last four bytes
//! of the jump instruction (which is true for x86_64).

use crate::{
    bc::{Instr, Loc, Program},
    CellType,
};

use super::{
    hpbf_context_extend, hpbf_context_input, hpbf_context_output, CodeGen, JmpPred, Reg, RegMem,
};

impl Reg {
    /// Return the register holding the given temporary or [`None`] if the temporary
    /// is stored on the stack and not in a register.
    fn tmp(tmp: usize) -> Option<Self> {
        // Note, we put callee saved register first, because the bytecode generator
        // prefers to allocate low-numbered temporaries and we want to avoid
        // excessive push and pops for rt calls.
        [
            Reg::R12,
            Reg::R13,
            Reg::R14,
            Reg::R15,
            Reg::Rsi,
            Reg::Rdi,
            Reg::Rdx,
            Reg::R8,
            Reg::R9,
            Reg::R10,
            Reg::R11,
        ]
        .get(tmp)
        .cloned()
    }

    /// Returns the register holding the context pointer.
    fn cxt() -> Self {
        Reg::Rbx
    }

    /// Returns the register holding the memory pointer.
    fn mem() -> Self {
        Reg::Rbp
    }

    /// Returns a register that can be used as a scratch register.
    fn scr0() -> Self {
        Reg::Rax
    }

    /// Returns a register that can be used as a scratch register. This register
    /// is guaranteed to be distinct from the one returned by [`Self::scr0`].
    fn scr1() -> Self {
        Reg::Rcx
    }
}

impl CodeGen {
    /// Get the memory parameter for accessing the memory pointer at the given offset.
    fn mem_param<C: CellType>(&self, idx: isize) -> RegMem {
        match C::BITS {
            8 => RegMem::Mem(Some(Reg::mem()), None, 1, idx as i32),
            16 => RegMem::Mem(Some(Reg::mem()), None, 1, 2 * idx as i32),
            32 => RegMem::Mem(Some(Reg::mem()), None, 1, 4 * idx as i32),
            64 => RegMem::Mem(Some(Reg::mem()), None, 1, 8 * idx as i32),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    /// Emit a store from a register into the memory cell at offset `idx` form
    /// the current memory pointer.
    fn emit_store_reg<C: CellType>(&mut self, idx: isize, reg: Reg) {
        match C::BITS {
            8 => self.emit_mov_rm8_r8(self.mem_param::<C>(idx), reg),
            16 => self.emit_mov_rm16_r16(self.mem_param::<C>(idx), reg),
            32 => self.emit_mov_rm32_r32(self.mem_param::<C>(idx), reg),
            64 => self.emit_mov_rm64_r64(self.mem_param::<C>(idx), reg),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    /// Emit a store of the 32 bit immediate into the memory cell at offset `idx`
    /// form the current memory pointer.
    fn emit_store_i32<C: CellType>(&mut self, idx: isize, imm: i32) {
        match C::BITS {
            8 => self.emit_mov_rm8_i8(self.mem_param::<C>(idx), imm as i8),
            16 => self.emit_mov_rm16_i16(self.mem_param::<C>(idx), imm as i16),
            32 => self.emit_mov_rm32_i32(self.mem_param::<C>(idx), imm),
            64 => self.emit_mov_rm64_i32(self.mem_param::<C>(idx), imm),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    /// Emit an addition of the given register to the memory cell at offset `idx`.
    fn emit_add_reg<C: CellType>(&mut self, idx: isize, reg: Reg) {
        match C::BITS {
            8 => self.emit_add_rm8_r8(self.mem_param::<C>(idx), reg),
            16 => self.emit_add_rm16_r16(self.mem_param::<C>(idx), reg),
            32 => self.emit_add_rm32_r32(self.mem_param::<C>(idx), reg),
            64 => self.emit_add_rm64_r64(self.mem_param::<C>(idx), reg),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    /// Emit an addition of the value in the memory cell at `idx` into `reg`.
    fn emit_add_to_reg<C: CellType>(&mut self, idx: isize, reg: Reg) {
        match C::BITS {
            8 => self.emit_add_r8_rm8(reg, self.mem_param::<C>(idx)),
            16 => self.emit_add_r16_rm16(reg, self.mem_param::<C>(idx)),
            32 => self.emit_add_r32_rm32(reg, self.mem_param::<C>(idx)),
            64 => self.emit_add_r64_rm64(reg, self.mem_param::<C>(idx)),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    /// Emit an addition of the 32 bit immediate to the memory cell at offset `idx`.
    fn emit_add_i32<C: CellType>(&mut self, idx: isize, imm: i32) {
        match C::BITS {
            8 => self.emit_add_rm8_i8(self.mem_param::<C>(idx), imm as i8),
            16 => self.emit_add_rm16_i16(self.mem_param::<C>(idx), imm as i16),
            32 => self.emit_add_rm32_i32(self.mem_param::<C>(idx), imm),
            64 => self.emit_add_rm64_i32(self.mem_param::<C>(idx), imm),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    /// Emit a subtraction of the given register to the memory cell at offset `idx`.
    fn emit_sub_reg<C: CellType>(&mut self, idx: isize, reg: Reg) {
        match C::BITS {
            8 => self.emit_sub_rm8_r8(self.mem_param::<C>(idx), reg),
            16 => self.emit_sub_rm16_r16(self.mem_param::<C>(idx), reg),
            32 => self.emit_sub_rm32_r32(self.mem_param::<C>(idx), reg),
            64 => self.emit_sub_rm64_r64(self.mem_param::<C>(idx), reg),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    /// Emit a subtraction of the value in the memory cell at `idx` into `reg`.
    fn emit_sub_to_reg<C: CellType>(&mut self, idx: isize, reg: Reg) {
        match C::BITS {
            8 => self.emit_sub_r8_rm8(reg, self.mem_param::<C>(idx)),
            16 => self.emit_sub_r16_rm16(reg, self.mem_param::<C>(idx)),
            32 => self.emit_sub_r32_rm32(reg, self.mem_param::<C>(idx)),
            64 => self.emit_sub_r64_rm64(reg, self.mem_param::<C>(idx)),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    /// Emit a load from the given memory cell at `idx` into rge register `reg`.
    fn emit_load<C: CellType>(&mut self, idx: isize, reg: Reg) {
        match C::BITS {
            8 => self.emit_mov_r64_rm8(reg, self.mem_param::<C>(idx)),
            16 => self.emit_mov_r64_rm16(reg, self.mem_param::<C>(idx)),
            32 => self.emit_mov_r64_rm32(reg, self.mem_param::<C>(idx)),
            64 => self.emit_mov_r64_rm64(reg, self.mem_param::<C>(idx)),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    /// Get the memory parameter for accessing the given temporary. This may either
    /// be a memory access or a register access depending on the temporary.
    fn tmp_param(&self, tmp: usize) -> RegMem {
        if let Some(reg) = Reg::tmp(tmp) {
            RegMem::Reg(reg)
        } else {
            RegMem::Mem(Some(Reg::Rsp), None, 1, 8 * tmp as i32)
        }
    }

    /// Compare the value of the given memory location with zero.
    fn emit_cmp_zero<C: CellType>(&mut self, idx: isize) {
        match C::BITS {
            8 => self.emit_cmp_rm8_i8(self.mem_param::<C>(idx), 0),
            16 => self.emit_cmp_rm16_i8(self.mem_param::<C>(idx), 0),
            32 => self.emit_cmp_rm32_i8(self.mem_param::<C>(idx), 0),
            64 => self.emit_cmp_rm64_i8(self.mem_param::<C>(idx), 0),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    /// Push all caller saved registers indicated by `live`. This is used before
    /// emitting a runtime call following the `sysv64` ABI.
    fn emit_pre_call(&mut self, mut live: u16) {
        live &= 0xfff0;
        let mut ll = live;
        while ll != 0 {
            let l = ll.trailing_zeros();
            self.emit_push_r64(Reg::tmp(l as usize).unwrap());
            ll -= 1 << l;
        }
        if live.count_ones().is_odd() {
            self.emit_add_rm64_i32(RegMem::Reg(Reg::Rsp), 8);
        }
    }

    /// Pop all caller saved registers indicated by `live`. This is used after
    /// emitting a runtime call following the `sysv64` ABI. The registers are
    /// poped in the reverse order in which they are pushed by [`Self::emit_pre_call`].
    fn emit_post_call(&mut self, live: u16) {
        let mut ll = live & 0xfff0;
        if ll.count_ones().is_odd() {
            self.emit_sub_rm64_i32(RegMem::Reg(Reg::Rsp), 8);
        }
        while ll != 0 {
            let l = 15 - ll.leading_zeros();
            self.emit_pop_r64(Reg::tmp(l as usize).unwrap());
            ll -= 1 << l;
        }
    }

    /// Emit a budget check. This should only be used in limited mode before each branch.
    fn emit_limit_check(&mut self) {
        self.emit_mov_r64_rm64(Reg::scr0(), RegMem::Mem(Some(Reg::cxt()), None, 1, 24));
        self.emit_cmp_rm64_i8(RegMem::Reg(Reg::scr0()), 2);
        self.emit_jcc_rel32(JmpPred::Below, 0);
        self.reloc_term.push(self.code.len() - 4);
        self.emit_sub_rm64_i32(RegMem::Reg(Reg::scr0()), 1);
        self.emit_mov_rm64_r64(RegMem::Mem(Some(Reg::cxt()), None, 1, 24), Reg::scr0());
    }

    /// Returns true if the given register can be used as a scratch register, that is
    /// it is not marked as live in the given `live`.
    fn can_use_as_scratch(&self, live: u16, tmp: usize) -> bool {
        if tmp < 11 {
            (live & (1 << tmp)) == 0
        } else {
            false
        }
    }
}

impl CodeGen {
    /// Emit the function prologue for the machine code function.
    /// Does the following:
    /// * Push all callee saved register.
    /// * Move the stack pointer to make room for the temporaries.
    /// * Move the context and memory pointers to the ones used by the compiler.
    pub fn emit_prologue(&mut self, temps: usize) {
        for reg in [Reg::Rbp, Reg::Rbx, Reg::R12, Reg::R13, Reg::R14, Reg::R15] {
            self.emit_push_r64(reg);
        }
        let aligned = if temps % 2 == 0 { temps + 1 } else { temps };
        self.emit_sub_rm64_i32(RegMem::Reg(Reg::Rsp), (aligned * 8) as i32);
        self.emit_mov_r64_rm64(Reg::cxt(), RegMem::Reg(Reg::Rdi));
        self.emit_mov_r64_rm64(Reg::mem(), RegMem::Reg(Reg::Rsi));
    }

    /// Emit the function epilogue for the machine code function.
    /// Does the following:
    /// * Setup return value (for both normal, and terminated path).
    /// * Move the stack pointer back to where it was.
    /// * Pop all callee saved register.
    /// * Return.
    pub fn emit_epilogue(&mut self, temps: usize) {
        self.emit_mov_r64_i64(Reg::Rax, 1);
        self.emit_jmp_rel8(0);
        let jmp_start = self.code.len();
        self.term = self.code.len();
        self.emit_mov_r64_i64(Reg::Rax, 0);
        self.code[jmp_start - 1] = (self.code.len() - jmp_start) as u8;
        let aligned = if temps % 2 == 0 { temps + 1 } else { temps };
        self.emit_add_rm64_i32(RegMem::Reg(Reg::Rsp), (aligned * 8) as i32);
        for reg in [Reg::R15, Reg::R14, Reg::R13, Reg::R12, Reg::Rbx, Reg::Rbp] {
            self.emit_pop_r64(reg);
        }
        self.emit_ret();
    }

    /// During compilation, branches and terminations generate relocations. These
    /// are fixed with this function by patching the machine code. Only 32bit pc
    /// relative relocations are used in this backed for simplicity.
    pub fn fix_relocations(&mut self) {
        for &(reloc, target) in &self.reloc_br {
            let pc_rel = (self.locations[target] as isize - reloc as isize - 4) as i32;
            self.code[reloc..reloc + 4].copy_from_slice(&pc_rel.to_le_bytes());
        }
        for &reloc in &self.reloc_term {
            let pc_rel = (self.term as isize - reloc as isize - 4) as i32;
            self.code[reloc..reloc + 4].copy_from_slice(&pc_rel.to_le_bytes());
        }
    }

    /// Emit the main part of the machine code function. Every instruction is emitted
    /// individually. Relocations will be generated for all termination paths and
    /// branch instructions that must later be fixed using [`Self::fix_relocations`].
    ///
    /// Some instructions have a lot of variations in operand and return locations.
    /// All of them are handles individually in the `match` below, with some special
    /// casing depending on the size of immediate values and whether temporaries are
    /// stored in registers of on the stack.
    pub fn emit_program<C: CellType>(&mut self, program: &Program<C>, limited: bool) {
        for (i, (&instr, &live)) in program.insts.iter().zip(program.live.iter()).enumerate() {
            self.locations.push(self.code.len());
            if limited {
                if let Instr::BrZ(_, _) | Instr::BrNZ(_, _) = instr {
                    self.emit_limit_check();
                }
            }
            match instr {
                Instr::Noop => { /* we skip nop */ }
                Instr::Mov(shift) => {
                    self.emit_add_rm64_i32(
                        RegMem::Reg(Reg::mem()),
                        (C::BITS / 8) as i32 * shift as i32,
                    );
                    self.emit_mov_r64_rm64(Reg::scr0(), RegMem::Reg(Reg::mem()));
                    self.emit_sub_r64_rm64(Reg::scr0(), RegMem::Mem(Some(Reg::cxt()), None, 1, 0));
                    if C::BITS != 8 {
                        self.emit_sar_r64_i8(RegMem::Reg(Reg::scr0()), (C::BITS / 8).ilog2() as u8);
                    }
                    let probe = if shift < 0 {
                        program.min_accessed
                    } else {
                        program.max_accessed
                    };
                    if probe != 0 {
                        self.emit_add_rm64_i32(RegMem::Reg(Reg::scr0()), probe as i32);
                    }
                    self.emit_cmp_r64_rm64(Reg::scr0(), RegMem::Mem(Some(Reg::cxt()), None, 1, 8));
                    self.emit_jcc_rel8(JmpPred::Below, 0);
                    let jmp_start = self.code.len();
                    if probe != 0 {
                        self.emit_sub_rm64_i32(RegMem::Reg(Reg::scr0()), probe as i32);
                    }
                    self.emit_mov_rm64_r64(RegMem::Mem(Some(Reg::cxt()), None, 1, 16), Reg::scr0());
                    self.emit_pre_call(live);
                    self.emit_mov_rm64_r64(RegMem::Reg(Reg::Rdi), Reg::cxt());
                    self.emit_mov_r64_i64(Reg::Rsi, program.min_accessed as i64);
                    self.emit_mov_r64_i64(Reg::Rdx, program.max_accessed as i64 + 1);
                    self.emit_mov_r64_i64(Reg::scr0(), hpbf_context_extend::<C> as i64);
                    self.emit_call_ind(RegMem::Reg(Reg::scr0()));
                    self.emit_post_call(live);
                    self.emit_mov_r64_rm64(Reg::mem(), RegMem::Mem(Some(Reg::cxt()), None, 1, 0));
                    if C::BITS == 8 {
                        self.emit_add_r64_rm64(
                            Reg::mem(),
                            RegMem::Mem(Some(Reg::cxt()), None, 1, 16),
                        );
                    } else {
                        self.emit_mov_r64_rm64(
                            Reg::scr0(),
                            RegMem::Mem(Some(Reg::cxt()), None, 1, 16),
                        );
                        self.emit_lea(
                            Reg::mem(),
                            RegMem::Mem(Some(Reg::mem()), Some(Reg::scr0()), C::BITS as u8 / 8, 0),
                        );
                    }
                    self.code[jmp_start - 1] = (self.code.len() - jmp_start) as u8;
                }
                Instr::Inp(dst) => {
                    self.emit_pre_call(live);
                    self.emit_mov_rm64_r64(RegMem::Reg(Reg::Rdi), Reg::cxt());
                    self.emit_mov_r64_i64(Reg::scr0(), hpbf_context_input::<C> as i64);
                    self.emit_call_ind(RegMem::Reg(Reg::scr0()));
                    self.emit_post_call(live);
                    self.emit_store_reg::<C>(dst, Reg::Rax);
                }
                Instr::Out(src) => {
                    self.emit_pre_call(live);
                    self.emit_mov_rm64_r64(RegMem::Reg(Reg::Rdi), Reg::cxt());
                    self.emit_load::<C>(src, Reg::Rsi);
                    self.emit_mov_r64_i64(Reg::scr0(), hpbf_context_output::<C> as i64);
                    self.emit_call_ind(RegMem::Reg(Reg::scr0()));
                    self.emit_post_call(live);
                    self.emit_cmp_rm8_i8(RegMem::Reg(Reg::Rax), 0);
                    self.emit_jcc_rel32(JmpPred::NotEqual, 0);
                    self.reloc_term.push(self.code.len() - 4);
                }
                Instr::BrZ(cond, off) => {
                    self.emit_cmp_zero::<C>(cond);
                    self.emit_jcc_rel32(JmpPred::Equal, 0);
                    self.reloc_br
                        .push((self.code.len() - 4, i.wrapping_add_signed(off)));
                }
                Instr::BrNZ(cond, off) => {
                    self.emit_cmp_zero::<C>(cond);
                    self.emit_jcc_rel32(JmpPred::NotEqual, 0);
                    self.reloc_br
                        .push((self.code.len() - 4, i.wrapping_add_signed(off)));
                }
                Instr::Copy(Loc::Mem(idx), Loc::Imm(imm)) => {
                    if let Ok(imm) = imm.into_i64().try_into() {
                        self.emit_store_i32::<C>(idx, imm);
                    } else {
                        self.emit_mov_r64_i64(Reg::scr0(), imm.into_i64());
                        self.emit_store_reg::<C>(idx, Reg::scr0());
                    }
                }
                Instr::Copy(Loc::Mem(idx0), Loc::Mem(idx1)) => {
                    self.emit_load::<C>(idx1, Reg::scr0());
                    self.emit_store_reg::<C>(idx0, Reg::scr0());
                }
                Instr::Copy(Loc::Mem(idx), Loc::Tmp(tmp)) => {
                    if let Some(reg) = Reg::tmp(tmp) {
                        self.emit_store_reg::<C>(idx, reg);
                    } else {
                        self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp));
                        self.emit_store_reg::<C>(idx, Reg::scr0());
                    }
                }
                Instr::Copy(Loc::Tmp(tmp), Loc::Imm(imm)) => {
                    if let Some(reg) = Reg::tmp(tmp) {
                        self.emit_mov_r64_i64(reg, imm.into_i64());
                    } else if let Ok(imm) = imm.into_i64().try_into() {
                        self.emit_mov_rm64_i32(self.tmp_param(tmp), imm);
                    } else {
                        self.emit_mov_r64_i64(Reg::scr0(), imm.into_i64());
                        self.emit_mov_rm64_r64(self.tmp_param(tmp), Reg::scr0());
                    }
                }
                Instr::Copy(Loc::Tmp(tmp), Loc::Mem(idx)) => {
                    if let Some(reg) = Reg::tmp(tmp) {
                        self.emit_load::<C>(idx, reg);
                    } else {
                        self.emit_load::<C>(idx, Reg::scr0());
                        self.emit_mov_rm64_r64(self.tmp_param(tmp), Reg::scr0());
                    }
                }
                Instr::Copy(Loc::Tmp(tmp0), Loc::Tmp(tmp1)) => {
                    match (Reg::tmp(tmp0), Reg::tmp(tmp1)) {
                        (Some(reg), _) => {
                            self.emit_mov_r64_rm64(reg, self.tmp_param(tmp1));
                        }
                        (None, Some(reg)) => {
                            self.emit_mov_rm64_r64(self.tmp_param(tmp0), reg);
                        }
                        (None, None) => {
                            self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                            self.emit_mov_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                        }
                    }
                }
                Instr::Add(Loc::Mem(idx0), Loc::Mem(idx1), Loc::Imm(imm)) => {
                    if idx0 == idx1 {
                        if let Ok(imm) = imm.into_i64().try_into() {
                            self.emit_add_i32::<C>(idx0, imm);
                        } else {
                            self.emit_mov_r64_i64(Reg::scr0(), imm.into_i64());
                            self.emit_add_reg::<C>(idx0, Reg::scr0());
                        }
                    } else {
                        self.emit_mov_r64_i64(Reg::scr0(), imm.into_i64());
                        self.emit_add_to_reg::<C>(idx1, Reg::scr0());
                        self.emit_store_reg::<C>(idx0, Reg::scr0());
                    }
                }
                Instr::Add(Loc::Mem(idx0), Loc::Mem(idx1), Loc::Tmp(tmp)) => {
                    if idx0 == idx1 {
                        if let Some(reg) = Reg::tmp(tmp) {
                            self.emit_add_reg::<C>(idx0, reg);
                        } else {
                            self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp));
                            self.emit_add_reg::<C>(idx0, Reg::scr0());
                        }
                    } else if self.can_use_as_scratch(live, tmp) {
                        let reg = Reg::tmp(tmp).unwrap();
                        self.emit_add_to_reg::<C>(idx1, reg);
                        self.emit_store_reg::<C>(idx0, reg);
                    } else {
                        self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp));
                        self.emit_add_to_reg::<C>(idx1, Reg::scr0());
                        self.emit_store_reg::<C>(idx0, Reg::scr0());
                    }
                }
                Instr::Add(Loc::Mem(idx0), Loc::Mem(idx1), Loc::Mem(idx2)) => {
                    if idx0 == idx1 {
                        self.emit_load::<C>(idx2, Reg::scr0());
                        self.emit_add_reg::<C>(idx0, Reg::scr0());
                    } else {
                        self.emit_load::<C>(idx2, Reg::scr0());
                        self.emit_add_to_reg::<C>(idx1, Reg::scr0());
                        self.emit_store_reg::<C>(idx0, Reg::scr0());
                    }
                }
                Instr::Add(Loc::Mem(idx), Loc::Tmp(tmp), Loc::Imm(imm)) => {
                    if let (Ok(imm), Some(reg)) = (imm.into_i64().try_into(), Reg::tmp(tmp)) {
                        if self.can_use_as_scratch(live, tmp) {
                            self.emit_add_rm64_i32(RegMem::Reg(reg), imm);
                            self.emit_store_reg::<C>(idx, reg);
                        } else {
                            self.emit_lea(Reg::scr0(), RegMem::Mem(Some(reg), None, 1, imm));
                            self.emit_store_reg::<C>(idx, Reg::scr0());
                        }
                    } else {
                        self.emit_mov_r64_i64(Reg::scr0(), imm.into_i64());
                        self.emit_add_r64_rm64(Reg::scr0(), self.tmp_param(tmp));
                        self.emit_store_reg::<C>(idx, Reg::scr0());
                    }
                }
                Instr::Add(Loc::Mem(idx), Loc::Tmp(tmp0), Loc::Tmp(tmp1)) => {
                    if self.can_use_as_scratch(live, tmp0) {
                        let reg0 = Reg::tmp(tmp0).unwrap();
                        self.emit_add_r64_rm64(reg0, self.tmp_param(tmp1));
                        self.emit_store_reg::<C>(idx, reg0);
                    } else if self.can_use_as_scratch(live, tmp1) {
                        let reg1 = Reg::tmp(tmp1).unwrap();
                        self.emit_add_r64_rm64(reg1, self.tmp_param(tmp0));
                        self.emit_store_reg::<C>(idx, reg1);
                    } else {
                        match (Reg::tmp(tmp0), Reg::tmp(tmp1)) {
                            (Some(reg0), Some(reg1)) => {
                                self.emit_lea(
                                    Reg::scr0(),
                                    RegMem::Mem(Some(reg0), Some(reg1), 1, 0),
                                );
                            }
                            (Some(reg0), _) => {
                                self.emit_mov_r64_rm64(Reg::scr0(), RegMem::Reg(reg0));
                                self.emit_add_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                            }
                            (_, _) => {
                                self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                                self.emit_add_r64_rm64(Reg::scr0(), self.tmp_param(tmp0));
                            }
                        }
                        self.emit_store_reg::<C>(idx, Reg::scr0());
                    }
                }
                Instr::Add(Loc::Tmp(tmp), Loc::Mem(idx), Loc::Imm(imm)) => {
                    if let Some(reg) = Reg::tmp(tmp) {
                        self.emit_mov_r64_i64(reg, imm.into_i64());
                        self.emit_add_to_reg::<C>(idx, reg);
                    } else {
                        self.emit_mov_r64_i64(Reg::scr0(), imm.into_i64());
                        self.emit_add_to_reg::<C>(idx, Reg::scr0());
                        self.emit_mov_rm64_r64(self.tmp_param(tmp), Reg::scr0());
                    }
                }
                Instr::Add(Loc::Tmp(tmp0), Loc::Mem(idx), Loc::Tmp(tmp1)) => {
                    if let Some(reg0) = Reg::tmp(tmp0) {
                        self.emit_mov_r64_rm64(reg0, self.tmp_param(tmp1));
                        self.emit_add_to_reg::<C>(idx, reg0);
                    } else {
                        self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                        self.emit_add_to_reg::<C>(idx, Reg::scr0());
                        self.emit_mov_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                    }
                }
                Instr::Add(Loc::Tmp(tmp), Loc::Mem(idx0), Loc::Mem(idx1)) => {
                    if let Some(reg) = Reg::tmp(tmp) {
                        self.emit_load::<C>(idx0, reg);
                        self.emit_add_to_reg::<C>(idx1, reg);
                    } else {
                        self.emit_load::<C>(idx0, Reg::scr0());
                        self.emit_add_to_reg::<C>(idx1, Reg::scr0());
                        self.emit_mov_rm64_r64(self.tmp_param(tmp), Reg::scr0());
                    }
                }
                Instr::Add(Loc::Tmp(tmp0), Loc::Tmp(tmp1), Loc::Imm(imm)) => {
                    if tmp0 == tmp1 {
                        if let Ok(imm) = imm.into_i64().try_into() {
                            self.emit_add_rm64_i32(self.tmp_param(tmp0), imm);
                        } else {
                            self.emit_mov_r64_i64(Reg::scr0(), imm.into_i64());
                            self.emit_add_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                        }
                    } else if let Ok(imm) = imm.into_i64().try_into() {
                        match (Reg::tmp(tmp0), Reg::tmp(tmp1)) {
                            (Some(reg0), Some(reg1)) => {
                                self.emit_lea(reg0, RegMem::Mem(Some(reg1), None, 1, imm));
                            }
                            (Some(reg0), _) => {
                                self.emit_mov_r64_rm64(reg0, self.tmp_param(tmp1));
                                self.emit_add_rm64_i32(RegMem::Reg(reg0), imm);
                            }
                            (_, _) => {
                                self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                                self.emit_add_rm64_i32(RegMem::Reg(Reg::scr0()), imm);
                                self.emit_add_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                            }
                        }
                    } else if let Some(reg0) = Reg::tmp(tmp0) {
                        self.emit_mov_r64_i64(reg0, imm.into_i64());
                        self.emit_mov_r64_rm64(reg0, self.tmp_param(tmp1));
                    } else {
                        self.emit_mov_r64_i64(Reg::scr0(), imm.into_i64());
                        self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                        self.emit_mov_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                    }
                }
                Instr::Add(Loc::Tmp(tmp0), Loc::Tmp(tmp1), Loc::Tmp(tmp2)) => {
                    if tmp0 == tmp1 {
                        if let Some(reg0) = Reg::tmp(tmp0) {
                            self.emit_add_r64_rm64(reg0, self.tmp_param(tmp2));
                        } else {
                            self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp2));
                            self.emit_add_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                        }
                    } else {
                        match (Reg::tmp(tmp0), Reg::tmp(tmp1), Reg::tmp(tmp2)) {
                            (Some(reg0), Some(reg1), Some(reg2)) => {
                                self.emit_lea(reg0, RegMem::Mem(Some(reg1), Some(reg2), 1, 0));
                            }
                            (Some(reg0), Some(_), _) if tmp0 != tmp2 => {
                                self.emit_mov_r64_rm64(reg0, self.tmp_param(tmp1));
                                self.emit_add_r64_rm64(reg0, self.tmp_param(tmp2));
                            }
                            (Some(reg0), _, _) => {
                                self.emit_mov_r64_rm64(reg0, self.tmp_param(tmp2));
                                self.emit_add_r64_rm64(reg0, self.tmp_param(tmp1));
                            }
                            (_, Some(_), _) => {
                                self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                                self.emit_add_r64_rm64(Reg::scr0(), self.tmp_param(tmp2));
                                self.emit_mov_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                            }
                            (_, _, _) => {
                                self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp2));
                                self.emit_add_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                                self.emit_mov_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                            }
                        }
                    }
                }
                Instr::Add(Loc::Tmp(tmp0), Loc::Tmp(tmp1), Loc::Mem(idx)) if tmp0 == tmp1 => {
                    if let Some(reg0) = Reg::tmp(tmp0) {
                        self.emit_add_to_reg::<C>(idx, reg0);
                    } else {
                        self.emit_load::<C>(idx, Reg::scr0());
                        self.emit_add_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                    }
                }
                Instr::Sub(Loc::Mem(idx0), Loc::Mem(idx1), Loc::Tmp(tmp)) => {
                    if idx0 == idx1 {
                        if let Some(reg) = Reg::tmp(tmp) {
                            self.emit_sub_reg::<C>(idx0, reg);
                        } else {
                            self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp));
                            self.emit_sub_reg::<C>(idx0, Reg::scr0());
                        }
                    } else {
                        self.emit_load::<C>(idx1, Reg::scr0());
                        self.emit_sub_r64_rm64(Reg::scr0(), self.tmp_param(tmp));
                        self.emit_store_reg::<C>(idx0, Reg::scr0());
                    }
                }
                Instr::Sub(Loc::Mem(idx0), Loc::Mem(idx1), Loc::Mem(idx2)) => {
                    if idx0 == idx1 {
                        self.emit_load::<C>(idx2, Reg::scr0());
                        self.emit_sub_reg::<C>(idx0, Reg::scr0());
                    } else {
                        self.emit_load::<C>(idx1, Reg::scr0());
                        self.emit_sub_to_reg::<C>(idx2, Reg::scr0());
                        self.emit_store_reg::<C>(idx0, Reg::scr0());
                    }
                }
                Instr::Sub(Loc::Mem(idx), Loc::Tmp(tmp0), Loc::Tmp(tmp1)) => {
                    if self.can_use_as_scratch(live, tmp0) {
                        let reg0 = Reg::tmp(tmp0).unwrap();
                        self.emit_sub_r64_rm64(reg0, self.tmp_param(tmp1));
                        self.emit_store_reg::<C>(idx, reg0);
                    } else {
                        self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp0));
                        self.emit_sub_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                        self.emit_store_reg::<C>(idx, Reg::scr0());
                    }
                }
                Instr::Sub(Loc::Mem(idx0), Loc::Tmp(tmp), Loc::Mem(idx1)) => {
                    if self.can_use_as_scratch(live, tmp) {
                        let reg = Reg::tmp(tmp).unwrap();
                        self.emit_sub_to_reg::<C>(idx1, reg);
                        self.emit_store_reg::<C>(idx0, reg);
                    } else {
                        self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp));
                        self.emit_sub_to_reg::<C>(idx1, Reg::scr0());
                        self.emit_store_reg::<C>(idx0, Reg::scr0());
                    }
                }
                Instr::Sub(Loc::Tmp(tmp0), Loc::Mem(idx), Loc::Tmp(tmp1)) => match Reg::tmp(tmp0) {
                    Some(reg0) if tmp0 != tmp1 => {
                        self.emit_load::<C>(idx, reg0);
                        self.emit_sub_r64_rm64(reg0, self.tmp_param(tmp1));
                    }
                    _ => {
                        self.emit_load::<C>(idx, Reg::scr0());
                        self.emit_sub_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                        self.emit_mov_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                    }
                },
                Instr::Sub(Loc::Tmp(tmp), Loc::Mem(idx0), Loc::Mem(idx1)) => {
                    if let Some(reg) = Reg::tmp(tmp) {
                        self.emit_load::<C>(idx0, reg);
                        self.emit_sub_to_reg::<C>(idx1, reg);
                    } else {
                        self.emit_load::<C>(idx0, Reg::scr0());
                        self.emit_sub_to_reg::<C>(idx1, Reg::scr0());
                        self.emit_mov_rm64_r64(self.tmp_param(tmp), Reg::scr0());
                    }
                }
                Instr::Sub(Loc::Tmp(tmp0), Loc::Tmp(tmp1), Loc::Tmp(tmp2)) => {
                    if tmp0 == tmp1 {
                        if let Some(reg0) = Reg::tmp(tmp0) {
                            self.emit_sub_r64_rm64(reg0, self.tmp_param(tmp2));
                        } else {
                            self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp2));
                            self.emit_sub_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                        }
                    } else {
                        match Reg::tmp(tmp0) {
                            Some(reg0) if tmp0 != tmp2 => {
                                self.emit_mov_r64_rm64(reg0, self.tmp_param(tmp1));
                                self.emit_sub_r64_rm64(reg0, self.tmp_param(tmp2));
                            }
                            _ => {
                                self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                                self.emit_sub_r64_rm64(Reg::scr0(), self.tmp_param(tmp2));
                                self.emit_mov_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                            }
                        }
                    }
                }
                Instr::Sub(Loc::Tmp(tmp0), Loc::Tmp(tmp1), Loc::Mem(idx)) => {
                    if tmp0 == tmp1 {
                        if let Some(reg0) = Reg::tmp(tmp0) {
                            self.emit_sub_to_reg::<C>(idx, reg0);
                        } else {
                            self.emit_load::<C>(idx, Reg::scr0());
                            self.emit_sub_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                        }
                    } else if let Some(reg0) = Reg::tmp(tmp0) {
                        self.emit_mov_r64_rm64(reg0, self.tmp_param(tmp1));
                        self.emit_sub_to_reg::<C>(idx, reg0);
                    } else {
                        self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                        self.emit_sub_to_reg::<C>(idx, Reg::scr0());
                        self.emit_mov_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                    }
                }
                Instr::Sub(Loc::Mem(idx), Loc::Imm(imm), Loc::Tmp(tmp)) => {
                    self.emit_mov_r64_i64(Reg::scr0(), imm.into_i64());
                    self.emit_sub_r64_rm64(Reg::scr0(), self.tmp_param(tmp));
                    self.emit_store_reg::<C>(idx, Reg::scr0());
                }
                Instr::Sub(Loc::Mem(idx0), Loc::Imm(imm), Loc::Mem(idx1)) => {
                    self.emit_mov_r64_i64(Reg::scr0(), imm.into_i64());
                    self.emit_sub_to_reg::<C>(idx1, Reg::scr0());
                    self.emit_store_reg::<C>(idx0, Reg::scr0());
                }
                Instr::Sub(Loc::Tmp(tmp0), Loc::Imm(imm), Loc::Tmp(tmp1)) => match Reg::tmp(tmp0) {
                    Some(reg) if tmp0 != tmp1 => {
                        self.emit_mov_r64_i64(reg, imm.into_i64());
                        self.emit_sub_r64_rm64(reg, self.tmp_param(tmp1));
                    }
                    _ => {
                        self.emit_mov_r64_i64(Reg::scr0(), imm.into_i64());
                        self.emit_sub_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                        self.emit_mov_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                    }
                },
                Instr::Sub(Loc::Tmp(tmp), Loc::Imm(imm), Loc::Mem(idx)) => {
                    if let Some(reg) = Reg::tmp(tmp) {
                        self.emit_mov_r64_i64(reg, imm.into_i64());
                        self.emit_sub_to_reg::<C>(idx, reg);
                    } else {
                        self.emit_mov_r64_i64(Reg::scr0(), imm.into_i64());
                        self.emit_sub_to_reg::<C>(idx, Reg::scr0());
                        self.emit_mov_rm64_r64(self.tmp_param(tmp), Reg::scr0());
                    }
                }
                Instr::Mul(Loc::Mem(idx0), Loc::Mem(idx1), Loc::Imm(imm)) => {
                    self.emit_load::<C>(idx1, Reg::scr0());
                    if let Ok(imm) = imm.into_i64().try_into() {
                        self.emit_mul_r64_rm64_i32(Reg::scr0(), RegMem::Reg(Reg::scr0()), imm);
                    } else {
                        self.emit_mov_r64_i64(Reg::scr1(), imm.into_i64());
                        self.emit_mul_r64_rm64(Reg::scr0(), RegMem::Reg(Reg::scr1()));
                    }
                    self.emit_store_reg::<C>(idx0, Reg::scr0());
                }
                Instr::Mul(Loc::Mem(idx0), Loc::Mem(idx1), Loc::Tmp(tmp)) => {
                    self.emit_load::<C>(idx1, Reg::scr0());
                    self.emit_mul_r64_rm64(Reg::scr0(), self.tmp_param(tmp));
                    self.emit_store_reg::<C>(idx0, Reg::scr0());
                }
                Instr::Mul(Loc::Mem(idx0), Loc::Mem(idx1), Loc::Mem(idx2)) => {
                    self.emit_load::<C>(idx1, Reg::scr0());
                    self.emit_load::<C>(idx2, Reg::scr1());
                    self.emit_mul_r64_rm64(Reg::scr0(), RegMem::Reg(Reg::scr1()));
                    self.emit_store_reg::<C>(idx0, Reg::scr0());
                }
                Instr::Mul(Loc::Mem(idx), Loc::Tmp(tmp), Loc::Imm(imm)) => {
                    if let (Ok(imm), Some(reg)) = (imm.into_i64().try_into(), Reg::tmp(tmp)) {
                        if self.can_use_as_scratch(live, tmp) {
                            self.emit_mul_r64_rm64_i32(reg, RegMem::Reg(reg), imm);
                            self.emit_store_reg::<C>(idx, reg);
                        } else {
                            self.emit_mul_r64_rm64_i32(Reg::scr0(), RegMem::Reg(reg), imm);
                            self.emit_store_reg::<C>(idx, Reg::scr0());
                        }
                    } else {
                        self.emit_mov_r64_i64(Reg::scr0(), imm.into_i64());
                        self.emit_mul_r64_rm64(Reg::scr0(), self.tmp_param(tmp));
                        self.emit_store_reg::<C>(idx, Reg::scr0());
                    }
                }
                Instr::Mul(Loc::Mem(idx), Loc::Tmp(tmp0), Loc::Tmp(tmp1)) => {
                    if self.can_use_as_scratch(live, tmp0) {
                        let reg0 = Reg::tmp(tmp0).unwrap();
                        self.emit_mul_r64_rm64(reg0, self.tmp_param(tmp1));
                        self.emit_store_reg::<C>(idx, reg0);
                    } else if self.can_use_as_scratch(live, tmp1) {
                        let reg1 = Reg::tmp(tmp1).unwrap();
                        self.emit_mul_r64_rm64(reg1, self.tmp_param(tmp0));
                        self.emit_store_reg::<C>(idx, reg1);
                    } else {
                        if Reg::tmp(tmp0).is_some() {
                            self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp0));
                            self.emit_mul_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                        } else {
                            self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                            self.emit_mul_r64_rm64(Reg::scr0(), self.tmp_param(tmp0));
                        }
                        self.emit_store_reg::<C>(idx, Reg::scr0());
                    }
                }
                Instr::Mul(Loc::Tmp(tmp), Loc::Mem(idx), Loc::Imm(imm)) => {
                    if let Some(reg) = Reg::tmp(tmp) {
                        self.emit_load::<C>(idx, reg);
                        if let Ok(imm) = imm.into_i64().try_into() {
                            self.emit_mul_r64_rm64_i32(reg, RegMem::Reg(reg), imm);
                        } else {
                            self.emit_mov_r64_i64(Reg::scr0(), imm.into_i64());
                            self.emit_mul_r64_rm64(reg, RegMem::Reg(Reg::scr0()));
                        }
                    } else {
                        self.emit_load::<C>(idx, Reg::scr0());
                        if let Ok(imm) = imm.into_i64().try_into() {
                            self.emit_mul_r64_rm64_i32(Reg::scr0(), RegMem::Reg(Reg::scr0()), imm);
                        } else {
                            self.emit_mov_r64_i64(Reg::scr1(), imm.into_i64());
                            self.emit_mul_r64_rm64(Reg::scr0(), RegMem::Reg(Reg::scr1()));
                        }
                        self.emit_mov_rm64_r64(self.tmp_param(tmp), Reg::scr0());
                    }
                }
                Instr::Mul(Loc::Tmp(tmp0), Loc::Mem(idx), Loc::Tmp(tmp1)) => match Reg::tmp(tmp0) {
                    Some(reg0) if tmp0 != tmp1 => {
                        self.emit_load::<C>(idx, reg0);
                        self.emit_mul_r64_rm64(reg0, self.tmp_param(tmp1));
                    }
                    _ => {
                        self.emit_load::<C>(idx, Reg::scr0());
                        self.emit_mul_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                        self.emit_mov_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                    }
                },
                Instr::Mul(Loc::Tmp(tmp), Loc::Mem(idx0), Loc::Mem(idx1)) => {
                    if let Some(reg) = Reg::tmp(tmp) {
                        self.emit_load::<C>(idx0, reg);
                        self.emit_load::<C>(idx1, Reg::scr0());
                        self.emit_mul_r64_rm64(reg, RegMem::Reg(Reg::scr0()));
                    } else {
                        self.emit_load::<C>(idx0, Reg::scr0());
                        self.emit_load::<C>(idx0, Reg::scr1());
                        self.emit_mul_r64_rm64(Reg::scr0(), RegMem::Reg(Reg::scr1()));
                        self.emit_mov_rm64_r64(self.tmp_param(tmp), Reg::scr0());
                    }
                }
                Instr::Mul(Loc::Tmp(tmp0), Loc::Tmp(tmp1), Loc::Imm(imm)) => {
                    match (Reg::tmp(tmp0), imm.into_i64().try_into()) {
                        (Some(reg0), Ok(imm)) => {
                            self.emit_mul_r64_rm64_i32(reg0, self.tmp_param(tmp1), imm);
                        }
                        (Some(reg0), _) if tmp0 != tmp1 => {
                            self.emit_mov_r64_i64(reg0, imm.into_i64());
                            self.emit_mul_r64_rm64(reg0, self.tmp_param(tmp1));
                        }
                        _ => {
                            self.emit_mov_r64_i64(Reg::scr0(), imm.into_i64());
                            self.emit_mul_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                            self.emit_mov_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                        }
                    }
                }
                Instr::Mul(Loc::Tmp(tmp0), Loc::Tmp(tmp1), Loc::Tmp(tmp2)) => {
                    if tmp0 == tmp1 {
                        if let Some(reg0) = Reg::tmp(tmp0) {
                            self.emit_mul_r64_rm64(reg0, self.tmp_param(tmp2));
                        } else {
                            self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp2));
                            self.emit_add_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                        }
                    } else {
                        match (Reg::tmp(tmp0), Reg::tmp(tmp1), Reg::tmp(tmp2)) {
                            (Some(reg0), Some(_), _) if tmp0 != tmp2 => {
                                self.emit_mov_r64_rm64(reg0, self.tmp_param(tmp1));
                                self.emit_mul_r64_rm64(reg0, self.tmp_param(tmp2));
                            }
                            (Some(reg0), _, _) => {
                                self.emit_mov_r64_rm64(reg0, self.tmp_param(tmp2));
                                self.emit_mul_r64_rm64(reg0, self.tmp_param(tmp1));
                            }
                            (_, Some(_), _) => {
                                self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                                self.emit_mul_r64_rm64(Reg::scr0(), self.tmp_param(tmp2));
                                self.emit_mov_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                            }
                            (_, _, _) => {
                                self.emit_mov_r64_rm64(Reg::scr0(), self.tmp_param(tmp2));
                                self.emit_mul_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                                self.emit_mov_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                            }
                        }
                    }
                }
                Instr::Mul(Loc::Tmp(tmp0), Loc::Tmp(tmp1), Loc::Mem(idx)) if tmp0 == tmp1 => {
                    if let Some(reg0) = Reg::tmp(tmp0) {
                        self.emit_load::<C>(idx, Reg::scr0());
                        self.emit_mul_r64_rm64(reg0, RegMem::Reg(Reg::scr0()));
                    } else {
                        self.emit_load::<C>(idx, Reg::scr0());
                        self.emit_mul_r64_rm64(Reg::scr0(), self.tmp_param(tmp1));
                        self.emit_mov_rm64_r64(self.tmp_param(tmp0), Reg::scr0());
                    }
                }
                _ => unimplemented!("bytecode instruction `{instr:?}`"),
            }
        }
        self.locations.push(self.code.len());
    }
}
