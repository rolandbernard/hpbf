//! A baseline JIT compiler using the bytecode infrastructure.

use std::{mem, ptr};

use crate::{
    bc::{self, Instr, Loc, Program},
    ir,
    runtime::Context,
    CellType, Error,
};

use super::{Executable, Executor};

/// Function type of the generated JIT function.
type HpbfEntry<'a, C> = unsafe extern "sysv64" fn(cxt: *mut Context<'a, C>, mem: *mut C) -> bool;

/// A baseline compiler that does some limited optimizing transformations of the
/// program and executes the result using a simple JIT compiler.
pub struct BaseJitCompiler<C: CellType> {
    bytecode: Program<C>,
}

/// Struct implementing the compilation.
/// Current register usage:
///   rsp -> stack pointer used for temps >= 11
///   rbx -> context pointer
///   rbp -> memory pointer
///   rax,rcx -> used for intermediate values
///   others -> temps < 11
struct CodeGen {
    locations: Vec<usize>,
    reloc_br: Vec<(usize, usize)>,
    reloc_term: Vec<usize>,
    term: usize,
    code: Vec<u8>,
}

#[derive(Clone, Copy, PartialEq)]
enum Reg {
    Rax = 0,
    Rcx,
    Rdx,
    Rbx,
    Rsp,
    Rbp,
    Rsi,
    Rdi,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

#[derive(Clone, Copy)]
enum RegMem {
    Reg(Reg),
    Mem(Option<Reg>, Option<Reg>, u8, i32),
}

#[derive(Clone, Copy, PartialEq)]
enum JmpPred {
    Below = 0x02,
    Equal = 0x04,
    NotEqual = 0x05,
}

impl Reg {
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

    fn cxt() -> Self {
        Reg::Rbx
    }

    fn mem() -> Self {
        Reg::Rbp
    }

    fn scr0() -> Self {
        Reg::Rax
    }

    fn scr1() -> Self {
        Reg::Rcx
    }

    fn enc(self) -> u8 {
        self as u8 & 7
    }
}

impl CodeGen {
    fn emit_rex(&mut self, wide: bool, reg: Option<Reg>, rm: RegMem) {
        let byte = 0x40
            + (wide as u8) * 0x8
            + ((reg.unwrap_or(Reg::Rax) as u8 >> 3) << 2)
            + match rm {
                RegMem::Reg(r) => r as u8 >> 3,
                RegMem::Mem(base, idx, _, _) => {
                    ((idx.unwrap_or(Reg::Rax) as u8 >> 3) << 1)
                        + (base.unwrap_or(Reg::Rax) as u8 >> 3)
                }
            };
        if byte != 0x40
            || reg.is_some_and(|r| [Reg::Rsp, Reg::Rbp, Reg::Rsi, Reg::Rdi].contains(&r))
        {
            self.code.push(byte);
        }
    }

    fn emit_modrm(&mut self, reg: Option<Reg>, op: u8, rm: RegMem) {
        match rm {
            RegMem::Reg(r) => {
                self.code
                    .push(0xc0 + (op << 3) + (reg.unwrap_or(Reg::Rax).enc() << 3) + r.enc());
            }
            RegMem::Mem(base, idx, mul, disp) => {
                let is_small = disp <= 127 && disp >= -128 && base.is_some();
                let is_zero = disp == 0 && base.is_some() && base.unwrap().enc() != 5;
                let mode = ((!is_zero && base.is_some()) as u8) << (6 + !is_small as u32);
                let modrm = mode + (op << 3) + (reg.unwrap_or(Reg::Rax).enc() << 3);
                if idx.is_none() && base.is_some() && base.unwrap().enc() != 4 {
                    self.code.push(modrm + base.unwrap().enc());
                } else {
                    self.code.push(modrm + 4);
                    self.code.push(
                        ((mul.ilog2() as u8) << 6)
                            + (idx.unwrap_or(Reg::Rsp).enc() << 3)
                            + base.unwrap_or(Reg::Rbp).enc(),
                    );
                }
                if !is_zero {
                    if is_small {
                        self.code.push(disp as u8);
                    } else {
                        self.code.extend_from_slice(&disp.to_le_bytes());
                    }
                }
            }
        }
    }

    fn emit_push_r64(&mut self, reg: Reg) {
        self.emit_rex(false, None, RegMem::Reg(reg));
        self.code.push(0x50 + reg.enc());
    }

    fn emit_pop_r64(&mut self, reg: Reg) {
        self.emit_rex(false, None, RegMem::Reg(reg));
        self.code.push(0x58 + reg.enc());
    }

    fn emit_add_rm64_i32(&mut self, rm: RegMem, imm: i32) {
        let is_small = imm <= 127 && imm >= -128;
        self.emit_rex(true, None, rm);
        self.code.push(if is_small { 0x83 } else { 0x81 });
        self.emit_modrm(None, 0, rm);
        if is_small {
            self.code.push(imm as u8);
        } else {
            self.code.extend_from_slice(&imm.to_le_bytes());
        }
    }

    fn emit_add_rm32_i32(&mut self, rm: RegMem, imm: i32) {
        let is_small = imm <= 127 && imm >= -128;
        self.emit_rex(false, None, rm);
        self.code.push(if is_small { 0x83 } else { 0x81 });
        self.emit_modrm(None, 0, rm);
        if is_small {
            self.code.push(imm as u8);
        } else {
            self.code.extend_from_slice(&imm.to_le_bytes());
        }
    }

    fn emit_add_rm16_i16(&mut self, rm: RegMem, imm: i16) {
        let is_small = imm <= 127 && imm >= -128;
        self.code.push(0x66);
        self.emit_rex(false, None, rm);
        self.code.push(if is_small { 0x83 } else { 0x81 });
        self.emit_modrm(None, 0, rm);
        if is_small {
            self.code.push(imm as u8);
        } else {
            self.code.extend_from_slice(&imm.to_le_bytes());
        }
    }

    fn emit_add_rm8_i8(&mut self, rm: RegMem, imm: i8) {
        self.emit_rex(false, None, rm);
        self.code.push(0x80);
        self.emit_modrm(None, 0, rm);
        self.code.push(imm as u8);
    }

    fn emit_add_rm64_r64(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(true, Some(src), dst);
        self.code.push(0x01);
        self.emit_modrm(Some(src), 0, dst);
    }

    fn emit_add_rm32_r32(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(false, Some(src), dst);
        self.code.push(0x01);
        self.emit_modrm(Some(src), 0, dst);
    }

    fn emit_add_rm16_r16(&mut self, dst: RegMem, src: Reg) {
        self.code.push(0x66);
        self.emit_rex(false, Some(src), dst);
        self.code.push(0x01);
        self.emit_modrm(Some(src), 0, dst);
    }

    fn emit_add_rm8_r8(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(false, Some(src), dst);
        self.code.push(0x00);
        self.emit_modrm(Some(src), 0, dst);
    }

    fn emit_add_r64_rm64(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(true, Some(dst), src);
        self.code.push(0x03);
        self.emit_modrm(Some(dst), 0, src);
    }

    fn emit_add_r32_rm32(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(false, Some(dst), src);
        self.code.push(0x03);
        self.emit_modrm(Some(dst), 0, src);
    }

    fn emit_add_r16_rm16(&mut self, dst: Reg, src: RegMem) {
        self.code.push(0x66);
        self.emit_rex(false, Some(dst), src);
        self.code.push(0x03);
        self.emit_modrm(Some(dst), 0, src);
    }

    fn emit_add_r8_rm8(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(false, Some(dst), src);
        self.code.push(0x02);
        self.emit_modrm(Some(dst), 0, src);
    }

    fn emit_sub_rm64_i32(&mut self, rm: RegMem, imm: i32) {
        let is_small = imm <= 127 && imm >= -128;
        self.emit_rex(true, None, rm);
        self.code.push(if is_small { 0x83 } else { 0x81 });
        self.emit_modrm(None, 5, rm);
        if is_small {
            self.code.push(imm as u8);
        } else {
            self.code.extend_from_slice(&imm.to_le_bytes());
        }
    }

    fn emit_sub_rm64_r64(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(true, Some(src), dst);
        self.code.push(0x29);
        self.emit_modrm(Some(src), 0, dst);
    }

    fn emit_sub_rm32_r32(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(false, Some(src), dst);
        self.code.push(0x29);
        self.emit_modrm(Some(src), 0, dst);
    }

    fn emit_sub_rm16_r16(&mut self, dst: RegMem, src: Reg) {
        self.code.push(0x66);
        self.emit_rex(false, Some(src), dst);
        self.code.push(0x29);
        self.emit_modrm(Some(src), 0, dst);
    }

    fn emit_sub_rm8_r8(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(false, Some(src), dst);
        self.code.push(0x28);
        self.emit_modrm(Some(src), 0, dst);
    }

    fn emit_sub_r64_rm64(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(true, Some(dst), src);
        self.code.push(0x2B);
        self.emit_modrm(Some(dst), 0, src);
    }

    fn emit_sub_r32_rm32(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(false, Some(dst), src);
        self.code.push(0x2B);
        self.emit_modrm(Some(dst), 0, src);
    }

    fn emit_sub_r16_rm16(&mut self, dst: Reg, src: RegMem) {
        self.code.push(0x66);
        self.emit_rex(false, Some(dst), src);
        self.code.push(0x2B);
        self.emit_modrm(Some(dst), 0, src);
    }

    fn emit_sub_r8_rm8(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(false, Some(dst), src);
        self.code.push(0x2a);
        self.emit_modrm(Some(dst), 0, src);
    }

    fn emit_mul_r64_rm64_i32(&mut self, dst: Reg, rm: RegMem, imm: i32) {
        let is_small = imm <= 127 && imm >= -128;
        self.emit_rex(true, Some(dst), rm);
        self.code.push(if is_small { 0x6b } else { 0x69 });
        self.emit_modrm(Some(dst), 0, rm);
        if is_small {
            self.code.push(imm as u8);
        } else {
            self.code.extend_from_slice(&imm.to_le_bytes());
        }
    }

    fn emit_mul_r64_rm64(&mut self, dst: Reg, rm: RegMem) {
        self.emit_rex(true, Some(dst), rm);
        self.code.push(0x0f);
        self.code.push(0xaf);
        self.emit_modrm(Some(dst), 0, rm);
    }

    fn emit_mov_r64_i64(&mut self, reg: Reg, imm: i64) {
        let is_small = imm <= i32::MAX as i64 && imm >= i32::MIN as i64;
        let is_small_uns = imm >= 0 && imm <= u32::MAX as i64;
        self.emit_rex(!is_small_uns, None, RegMem::Reg(reg));
        if is_small || is_small_uns {
            self.code.push(0xc7);
            self.emit_modrm(None, 0, RegMem::Reg(reg));
            self.code.extend_from_slice(&(imm as i32).to_le_bytes());
        } else {
            self.code.push(0xb8 + reg.enc());
            self.code.extend_from_slice(&imm.to_le_bytes());
        }
    }

    fn emit_mov_rm64_i32(&mut self, rm: RegMem, imm: i32) {
        self.emit_rex(true, None, rm);
        self.code.push(0xc7);
        self.emit_modrm(None, 0, rm);
        self.code.extend_from_slice(&imm.to_le_bytes());
    }

    fn emit_mov_rm32_i32(&mut self, rm: RegMem, imm: i32) {
        self.emit_rex(false, None, rm);
        self.code.push(0xc7);
        self.emit_modrm(None, 0, rm);
        self.code.extend_from_slice(&imm.to_le_bytes());
    }

    fn emit_mov_rm16_i16(&mut self, rm: RegMem, imm: i16) {
        self.code.push(0x66);
        self.emit_rex(false, None, rm);
        self.code.push(0xc7);
        self.emit_modrm(None, 0, rm);
        self.code.extend_from_slice(&imm.to_le_bytes());
    }

    fn emit_mov_rm8_i8(&mut self, rm: RegMem, imm: i8) {
        self.emit_rex(false, None, rm);
        self.code.push(0xc6);
        self.emit_modrm(None, 0, rm);
        self.code.push(imm as u8);
    }

    fn emit_mov_r64_rm64(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(true, Some(dst), src);
        self.code.push(0x8b);
        self.emit_modrm(Some(dst), 0, src);
    }

    fn emit_mov_rm64_r64(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(true, Some(src), dst);
        self.code.push(0x89);
        self.emit_modrm(Some(src), 0, dst);
    }

    fn emit_mov_r64_rm32(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(false, Some(dst), src);
        self.code.push(0x8b);
        self.emit_modrm(Some(dst), 0, src);
    }

    fn emit_mov_rm32_r32(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(false, Some(src), dst);
        self.code.push(0x89);
        self.emit_modrm(Some(src), 0, dst);
    }

    fn emit_mov_r64_rm16(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(false, Some(dst), src);
        self.code.push(0x0f);
        self.code.push(0xb7);
        self.emit_modrm(Some(dst), 0, src);
    }

    fn emit_mov_rm16_r16(&mut self, dst: RegMem, src: Reg) {
        self.code.push(0x66);
        self.emit_rex(false, Some(src), dst);
        self.code.push(0x89);
        self.emit_modrm(Some(src), 0, dst);
    }

    fn emit_mov_r64_rm8(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(false, Some(dst), src);
        self.code.push(0x0f);
        self.code.push(0xb6);
        self.emit_modrm(Some(dst), 0, src);
    }

    fn emit_mov_rm8_r8(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(false, Some(src), dst);
        self.code.push(0x88);
        self.emit_modrm(Some(src), 0, dst);
    }

    fn emit_lea(&mut self, dst: Reg, addr: RegMem) {
        self.emit_rex(true, Some(dst), addr);
        self.code.push(0x8d);
        self.emit_modrm(Some(dst), 0, addr);
    }

    fn emit_cmp_r64_rm64(&mut self, fst: Reg, snd: RegMem) {
        self.emit_rex(true, Some(fst), snd);
        self.code.push(0x3b);
        self.emit_modrm(Some(fst), 0, snd);
    }

    fn emit_cmp_rm64_i8(&mut self, rm: RegMem, imm: i8) {
        self.emit_rex(true, None, rm);
        self.code.push(0x83);
        self.emit_modrm(None, 7, rm);
        self.code.push(imm as u8);
    }

    fn emit_cmp_rm32_i8(&mut self, rm: RegMem, imm: i8) {
        self.emit_rex(false, None, rm);
        self.code.push(0x83);
        self.emit_modrm(None, 7, rm);
        self.code.push(imm as u8);
    }

    fn emit_cmp_rm16_i8(&mut self, rm: RegMem, imm: i8) {
        self.code.push(0x66);
        self.emit_rex(false, None, rm);
        self.code.push(0x83);
        self.emit_modrm(None, 7, rm);
        self.code.push(imm as u8);
    }

    fn emit_cmp_rm8_i8(&mut self, rm: RegMem, imm: i8) {
        self.emit_rex(false, None, rm);
        self.code.push(0x80);
        self.emit_modrm(None, 7, rm);
        self.code.push(imm as u8);
    }

    fn emit_jmp_rel8(&mut self, off: i8) {
        self.code.push(0xeb);
        self.code.push(off as u8);
    }

    fn emit_jcc_rel8(&mut self, pred: JmpPred, off: i8) {
        self.code.push(0x70 + pred as u8);
        self.code.push(off as u8);
    }

    fn emit_jcc_rel32(&mut self, pred: JmpPred, off: i32) {
        self.code.push(0x0f);
        self.code.push(0x80 + pred as u8);
        self.code.extend_from_slice(&off.to_le_bytes());
    }

    fn emit_sar_r64_i8(&mut self, dst: RegMem, shift: u8) {
        self.emit_rex(true, None, dst);
        self.code.push(0xc1);
        self.emit_modrm(None, 7, dst);
        self.code.push(shift);
    }

    fn emit_ret(&mut self) {
        self.code.push(0xc3);
    }

    fn emit_call_ind(&mut self, target: RegMem) {
        self.code.push(0xff);
        self.emit_modrm(None, 2, target);
    }
}

impl CodeGen {
    fn emit_prologue(&mut self, temps: usize) {
        for reg in [Reg::Rbp, Reg::Rbx, Reg::R12, Reg::R13, Reg::R14, Reg::R15] {
            self.emit_push_r64(reg);
        }
        let aligned = if temps % 2 == 0 { temps + 1 } else { temps };
        self.emit_sub_rm64_i32(RegMem::Reg(Reg::Rsp), (aligned * 8) as i32);
        self.emit_mov_r64_rm64(Reg::cxt(), RegMem::Reg(Reg::Rdi));
        self.emit_mov_r64_rm64(Reg::mem(), RegMem::Reg(Reg::Rsi));
    }

    fn emit_epilogue(&mut self, temps: usize) {
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

    fn mem_param<C: CellType>(&self, idx: isize) -> RegMem {
        match C::BITS {
            8 => RegMem::Mem(Some(Reg::mem()), None, 1, idx as i32),
            16 => RegMem::Mem(Some(Reg::mem()), None, 1, 2 * idx as i32),
            32 => RegMem::Mem(Some(Reg::mem()), None, 1, 4 * idx as i32),
            64 => RegMem::Mem(Some(Reg::mem()), None, 1, 8 * idx as i32),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    fn emit_store_reg<C: CellType>(&mut self, idx: isize, reg: Reg) {
        match C::BITS {
            8 => self.emit_mov_rm8_r8(self.mem_param::<C>(idx), reg),
            16 => self.emit_mov_rm16_r16(self.mem_param::<C>(idx), reg),
            32 => self.emit_mov_rm32_r32(self.mem_param::<C>(idx), reg),
            64 => self.emit_mov_rm64_r64(self.mem_param::<C>(idx), reg),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    fn emit_store_i32<C: CellType>(&mut self, idx: isize, imm: i32) {
        match C::BITS {
            8 => self.emit_mov_rm8_i8(self.mem_param::<C>(idx), imm as i8),
            16 => self.emit_mov_rm16_i16(self.mem_param::<C>(idx), imm as i16),
            32 => self.emit_mov_rm32_i32(self.mem_param::<C>(idx), imm),
            64 => self.emit_mov_rm64_i32(self.mem_param::<C>(idx), imm),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    fn emit_add_reg<C: CellType>(&mut self, idx: isize, reg: Reg) {
        match C::BITS {
            8 => self.emit_add_rm8_r8(self.mem_param::<C>(idx), reg),
            16 => self.emit_add_rm16_r16(self.mem_param::<C>(idx), reg),
            32 => self.emit_add_rm32_r32(self.mem_param::<C>(idx), reg),
            64 => self.emit_add_rm64_r64(self.mem_param::<C>(idx), reg),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    fn emit_add_to_reg<C: CellType>(&mut self, idx: isize, reg: Reg) {
        match C::BITS {
            8 => self.emit_add_r8_rm8(reg, self.mem_param::<C>(idx)),
            16 => self.emit_add_r16_rm16(reg, self.mem_param::<C>(idx)),
            32 => self.emit_add_r32_rm32(reg, self.mem_param::<C>(idx)),
            64 => self.emit_add_r64_rm64(reg, self.mem_param::<C>(idx)),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    fn emit_add_i32<C: CellType>(&mut self, idx: isize, imm: i32) {
        match C::BITS {
            8 => self.emit_add_rm8_i8(self.mem_param::<C>(idx), imm as i8),
            16 => self.emit_add_rm16_i16(self.mem_param::<C>(idx), imm as i16),
            32 => self.emit_add_rm32_i32(self.mem_param::<C>(idx), imm),
            64 => self.emit_add_rm64_i32(self.mem_param::<C>(idx), imm),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    fn emit_sub_reg<C: CellType>(&mut self, idx: isize, reg: Reg) {
        match C::BITS {
            8 => self.emit_sub_rm8_r8(self.mem_param::<C>(idx), reg),
            16 => self.emit_sub_rm16_r16(self.mem_param::<C>(idx), reg),
            32 => self.emit_sub_rm32_r32(self.mem_param::<C>(idx), reg),
            64 => self.emit_sub_rm64_r64(self.mem_param::<C>(idx), reg),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    fn emit_sub_to_reg<C: CellType>(&mut self, idx: isize, reg: Reg) {
        match C::BITS {
            8 => self.emit_sub_r8_rm8(reg, self.mem_param::<C>(idx)),
            16 => self.emit_sub_r16_rm16(reg, self.mem_param::<C>(idx)),
            32 => self.emit_sub_r32_rm32(reg, self.mem_param::<C>(idx)),
            64 => self.emit_sub_r64_rm64(reg, self.mem_param::<C>(idx)),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    fn emit_load<C: CellType>(&mut self, idx: isize, reg: Reg) {
        match C::BITS {
            8 => self.emit_mov_r64_rm8(reg, self.mem_param::<C>(idx)),
            16 => self.emit_mov_r64_rm16(reg, self.mem_param::<C>(idx)),
            32 => self.emit_mov_r64_rm32(reg, self.mem_param::<C>(idx)),
            64 => self.emit_mov_r64_rm64(reg, self.mem_param::<C>(idx)),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

    fn tmp_param(&self, tmp: usize) -> RegMem {
        if let Some(reg) = Reg::tmp(tmp) {
            RegMem::Reg(reg)
        } else {
            RegMem::Mem(Some(Reg::Rsp), None, 1, 8 * tmp as i32)
        }
    }

    fn emit_cmp_zero<C: CellType>(&mut self, idx: isize) {
        match C::BITS {
            8 => self.emit_cmp_rm8_i8(self.mem_param::<C>(idx), 0),
            16 => self.emit_cmp_rm16_i8(self.mem_param::<C>(idx), 0),
            32 => self.emit_cmp_rm32_i8(self.mem_param::<C>(idx), 0),
            64 => self.emit_cmp_rm64_i8(self.mem_param::<C>(idx), 0),
            _ => unimplemented!("bit width {}", C::BITS),
        }
    }

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

    fn emit_limit_check(&mut self) {
        self.emit_mov_r64_rm64(Reg::scr0(), RegMem::Mem(Some(Reg::cxt()), None, 1, 24));
        self.emit_cmp_rm64_i8(RegMem::Reg(Reg::scr0()), 2);
        self.emit_jcc_rel32(JmpPred::Below, 0);
        self.reloc_term.push(self.code.len() - 4);
        self.emit_sub_rm64_i32(RegMem::Reg(Reg::scr0()), 1);
        self.emit_mov_rm64_r64(RegMem::Mem(Some(Reg::cxt()), None, 1, 24), Reg::scr0());
    }

    fn can_use_as_scratch(&self, live: u16, tmp: usize) -> bool {
        if tmp < 10 {
            (live & (1 << tmp)) == 0
        } else {
            false
        }
    }

    fn emit_program<C: CellType>(&mut self, program: &Program<C>, limited: bool) {
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

    fn fix_relocations(&mut self) {
        for &(reloc, target) in &self.reloc_br {
            let pc_rel = (self.locations[target] as isize - reloc as isize - 4) as i32;
            self.code[reloc..reloc + 4].copy_from_slice(&pc_rel.to_le_bytes());
        }
        for &reloc in &self.reloc_term {
            let pc_rel = (self.term as isize - reloc as isize - 4) as i32;
            self.code[reloc..reloc + 4].copy_from_slice(&pc_rel.to_le_bytes());
        }
    }
}

impl<C: CellType> BaseJitCompiler<C> {
    /// Return the machine code generated by this compiler.
    pub fn print_mc(&self, limit: bool) -> Vec<u8> {
        self.compile_program(limit)
    }

    /// Generate, from the bytecode, the corresponding machine code.
    fn compile_program(&self, limited: bool) -> Vec<u8> {
        let mut code_gen = CodeGen {
            locations: Vec::new(),
            reloc_br: Vec::new(),
            reloc_term: Vec::new(),
            term: 0,
            code: Vec::new(),
        };
        code_gen.emit_prologue(self.bytecode.temps);
        code_gen.emit_program(&self.bytecode, limited);
        code_gen.emit_epilogue(self.bytecode.temps);
        code_gen.fix_relocations();
        code_gen.code
    }

    /// Allocate executable memory, copy the code into it, and enter the JITed code.
    fn enter_jit_code(&self, cxt: &mut Context<C>, code: Vec<u8>) -> bool {
        cxt.memory
            .make_accessible(self.bytecode.min_accessed, self.bytecode.max_accessed + 1);
        // Lets guess the page size is 4 or 16 KiB.
        const PAGE_SIZE: usize = 1 << 14;
        let result;
        unsafe {
            let len = (code.len() + PAGE_SIZE) & !(PAGE_SIZE - 1);
            let code_mem = libc::mmap(
                ptr::null_mut(),
                len,
                libc::PROT_EXEC | libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_ANONYMOUS | libc::MAP_PRIVATE,
                0,
                0,
            ) as *mut u8;
            assert!(
                code_mem as isize != -1,
                "failed mmap executable memory region"
            );
            ptr::copy_nonoverlapping(code.as_ptr(), code_mem, code.len());
            let mem_ptr = cxt.memory.current_ptr();
            let entry = mem::transmute::<_, HpbfEntry<C>>(code_mem);
            result = entry(cxt, mem_ptr);
            assert!(
                libc::munmap(code_mem as *mut _, len) == 0,
                "failed to munmap jit memory"
            );
        }
        result
    }

    /// Execute in the given context using the JIT compiler.
    fn execute_in<'a>(&self, cxt: &mut Context<'a, C>) {
        let code = self.compile_program(false);
        self.enter_jit_code(cxt, code);
    }

    /// Execute in the given context using the JIT compiler.
    fn execute_limited_in(&self, cxt: &mut Context<C>, budget: usize) -> bool {
        let code = self.compile_program(true);
        cxt.budget = budget;
        self.enter_jit_code(cxt, code)
    }
}

impl<'code, C: CellType> Executor<'code, C> for BaseJitCompiler<C> {
    fn create(code: &str, opt: u32) -> Result<Self, Error> {
        let mut program = ir::Program::<C>::parse(code)?;
        program = program.optimize(opt);
        let bytecode = bc::CodeGen::translate(&program, 11, false);
        Ok(BaseJitCompiler { bytecode })
    }
}

impl<C: CellType> Executable<C> for BaseJitCompiler<C> {
    fn execute(&self, context: &mut Context<C>) -> Result<(), Error> {
        self.execute_in(context);
        Ok(())
    }

    fn execute_limited(&self, context: &mut Context<C>, instr: usize) -> Result<bool, Error> {
        Ok(self.execute_limited_in(context, instr))
    }
}

/// Runtime function. Extends the memory buffer and moves the offset to make the range
/// from `min` (inclusive) to `max` (exclusive) accessible.
extern "sysv64" fn hpbf_context_extend<C: CellType>(
    cxt: &mut Context<'static, C>,
    min: isize,
    max: isize,
) {
    cxt.memory.make_accessible(min, max);
}

/// Runtime function. Get a value form the input, or zero in case the input closed.
extern "sysv64" fn hpbf_context_input<C: CellType>(cxt: &mut Context<'static, C>) -> C {
    C::from_u8(cxt.input().unwrap_or(0))
}

/// Runtime function. Print the given value to the output and return true if the output closed.
extern "sysv64" fn hpbf_context_output<C: CellType>(
    cxt: &mut Context<'static, u8>,
    value: C,
) -> bool {
    cxt.output(value.into_u8()).is_none()
}

executor_tests!(BaseJitCompiler);
same_as_inplace_tests!(BaseJitCompiler);
