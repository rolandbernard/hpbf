//! This module contains some basic utilities for emitting x86_64 machine code.
//! Note that this can handle only the minimal set of instructions needed by the
//! actual backend, and is not nearly an exhaustive implementation.

use super::CodeGen;

/// General purpose register available on x86_64.
#[derive(Clone, Copy, PartialEq)]
pub enum Reg {
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

/// Represents the things that can be encoded using the ModR/M encoding.
#[derive(Clone, Copy)]
pub enum RegMem {
    Reg(Reg),
    Mem(Option<Reg>, Option<Reg>, u8, i32),
}

/// Type of branch conditions. This includes only the ones used in the backed.
#[derive(Clone, Copy, PartialEq)]
pub enum JmpPred {
    Below = 0x02,
    Equal = 0x04,
    NotEqual = 0x05,
}

impl Reg {
    /// Small helper function that returns the lower three bits of the register
    /// encoding. Useful for encoding instructions.
    fn enc(self) -> u8 {
        self as u8 & 7
    }
}

impl CodeGen {
    /// Emit the REX prefix is required. `wide` indicates whether we need this byte
    /// to make the operation 64 bit, `isb` indicates whether this is used with
    /// a byte register opcode and therefore we need the REX prefix to encode some
    /// registers. `reg` is the register in the and `rm` the register/memory accessed
    /// by the instruction.
    fn emit_rex(&mut self, wide: bool, isb: bool, reg: Option<Reg>, rm: RegMem) {
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
            || (isb && reg.is_some_and(|r| [Reg::Rsp, Reg::Rbp, Reg::Rsi, Reg::Rdi].contains(&r)))
        {
            self.code.push(byte);
        }
    }

    /// Emit the ModR/M byte and possibly, if needed also the SIB byte to encode
    /// the requested addressing mode. `reg` specifies the register in the instruction,
    /// and if that is not given, `op` may be necessary to specify part of the opcode.
    fn emit_modrm(&mut self, reg: Option<Reg>, op: u8, rm: RegMem) {
        match rm {
            RegMem::Reg(r) => {
                self.code
                    .push(0xc0 + (op << 3) + (reg.unwrap_or(Reg::Rax).enc() << 3) + r.enc());
            }
            RegMem::Mem(base, idx, mul, disp) => {
                let is_small = (-128..=127).contains(&disp) && base.is_some();
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

    pub fn emit_push_r64(&mut self, reg: Reg) {
        self.emit_rex(false, false, None, RegMem::Reg(reg));
        self.code.push(0x50 + reg.enc());
    }

    pub fn emit_pop_r64(&mut self, reg: Reg) {
        self.emit_rex(false, false, None, RegMem::Reg(reg));
        self.code.push(0x58 + reg.enc());
    }

    /// Automatically selects between the 32 bit or 8 bit immediate version.
    pub fn emit_add_rm64_i32(&mut self, rm: RegMem, imm: i32) {
        if imm == -1 {
            self.emit_dec_rm64(rm);
        } else if imm == 1 {
            self.emit_inc_rm64(rm);
        } else {
            let is_small = (-128..=127).contains(&imm);
            self.emit_rex(true, false, None, rm);
            self.code.push(if is_small { 0x83 } else { 0x81 });
            self.emit_modrm(None, 0, rm);
            if is_small {
                self.code.push(imm as u8);
            } else {
                self.code.extend_from_slice(&imm.to_le_bytes());
            }
        }
    }

    /// Automatically selects between the 32 bit or 8 bit immediate version.
    pub fn emit_add_rm32_i32(&mut self, rm: RegMem, imm: i32) {
        if imm == -1 {
            self.emit_dec_rm32(rm);
        } else if imm == 1 {
            self.emit_inc_rm32(rm);
        } else {
            let is_small = (-128..=127).contains(&imm);
            self.emit_rex(false, false, None, rm);
            self.code.push(if is_small { 0x83 } else { 0x81 });
            self.emit_modrm(None, 0, rm);
            if is_small {
                self.code.push(imm as u8);
            } else {
                self.code.extend_from_slice(&imm.to_le_bytes());
            }
        }
    }

    /// Automatically selects between the 16 bit or 8 bit immediate version.
    pub fn emit_add_rm16_i16(&mut self, rm: RegMem, imm: i16) {
        if imm == -1 {
            self.emit_dec_rm16(rm);
        } else if imm == 1 {
            self.emit_inc_rm16(rm);
        } else {
            let is_small = (-128..=127).contains(&imm);
            self.code.push(0x66);
            self.emit_rex(false, false, None, rm);
            self.code.push(if is_small { 0x83 } else { 0x81 });
            self.emit_modrm(None, 0, rm);
            if is_small {
                self.code.push(imm as u8);
            } else {
                self.code.extend_from_slice(&imm.to_le_bytes());
            }
        }
    }

    pub fn emit_add_rm8_i8(&mut self, rm: RegMem, imm: i8) {
        if imm == -1 {
            self.emit_dec_rm8(rm);
        } else if imm == 1 {
            self.emit_inc_rm8(rm);
        } else {
            self.emit_rex(false, true, None, rm);
            self.code.push(0x80);
            self.emit_modrm(None, 0, rm);
            self.code.push(imm as u8);
        }
    }

    pub fn emit_add_rm64_r64(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(true, false, Some(src), dst);
        self.code.push(0x01);
        self.emit_modrm(Some(src), 0, dst);
    }

    pub fn emit_add_rm32_r32(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(false, false, Some(src), dst);
        self.code.push(0x01);
        self.emit_modrm(Some(src), 0, dst);
    }

    pub fn emit_add_rm16_r16(&mut self, dst: RegMem, src: Reg) {
        self.code.push(0x66);
        self.emit_rex(false, false, Some(src), dst);
        self.code.push(0x01);
        self.emit_modrm(Some(src), 0, dst);
    }

    pub fn emit_add_rm8_r8(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(false, true, Some(src), dst);
        self.code.push(0x00);
        self.emit_modrm(Some(src), 0, dst);
    }

    pub fn emit_add_r64_rm64(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(true, false, Some(dst), src);
        self.code.push(0x03);
        self.emit_modrm(Some(dst), 0, src);
    }

    pub fn emit_add_r32_rm32(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(false, false, Some(dst), src);
        self.code.push(0x03);
        self.emit_modrm(Some(dst), 0, src);
    }

    pub fn emit_add_r16_rm16(&mut self, dst: Reg, src: RegMem) {
        self.code.push(0x66);
        self.emit_rex(false, false, Some(dst), src);
        self.code.push(0x03);
        self.emit_modrm(Some(dst), 0, src);
    }

    pub fn emit_add_r8_rm8(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(false, true, Some(dst), src);
        self.code.push(0x02);
        self.emit_modrm(Some(dst), 0, src);
    }

    /// Automatically selects between the 32 bit or 8 bit immediate version.
    pub fn emit_sub_rm64_i32(&mut self, rm: RegMem, imm: i32) {
        if imm == 1 {
            self.emit_dec_rm64(rm);
        } else if imm == -1 {
            self.emit_inc_rm64(rm);
        } else {
            let is_small = (-128..=127).contains(&imm);
            self.emit_rex(true, false, None, rm);
            self.code.push(if is_small { 0x83 } else { 0x81 });
            self.emit_modrm(None, 5, rm);
            if is_small {
                self.code.push(imm as u8);
            } else {
                self.code.extend_from_slice(&imm.to_le_bytes());
            }
        }
    }

    pub fn emit_sub_rm64_r64(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(true, false, Some(src), dst);
        self.code.push(0x29);
        self.emit_modrm(Some(src), 0, dst);
    }

    pub fn emit_sub_rm32_r32(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(false, false, Some(src), dst);
        self.code.push(0x29);
        self.emit_modrm(Some(src), 0, dst);
    }

    pub fn emit_sub_rm16_r16(&mut self, dst: RegMem, src: Reg) {
        self.code.push(0x66);
        self.emit_rex(false, false, Some(src), dst);
        self.code.push(0x29);
        self.emit_modrm(Some(src), 0, dst);
    }

    pub fn emit_sub_rm8_r8(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(false, true, Some(src), dst);
        self.code.push(0x28);
        self.emit_modrm(Some(src), 0, dst);
    }

    pub fn emit_sub_r64_rm64(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(true, false, Some(dst), src);
        self.code.push(0x2B);
        self.emit_modrm(Some(dst), 0, src);
    }

    pub fn emit_sub_r32_rm32(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(false, false, Some(dst), src);
        self.code.push(0x2B);
        self.emit_modrm(Some(dst), 0, src);
    }

    pub fn emit_sub_r16_rm16(&mut self, dst: Reg, src: RegMem) {
        self.code.push(0x66);
        self.emit_rex(false, false, Some(dst), src);
        self.code.push(0x2B);
        self.emit_modrm(Some(dst), 0, src);
    }

    pub fn emit_sub_r8_rm8(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(false, true, Some(dst), src);
        self.code.push(0x2a);
        self.emit_modrm(Some(dst), 0, src);
    }

    /// Automatically selects between the 32 bit or 8 bit immediate version.
    pub fn emit_mul_r64_rm64_i32(&mut self, dst: Reg, rm: RegMem, imm: i32) {
        let is_small = (-128..=127).contains(&imm);
        self.emit_rex(true, false, Some(dst), rm);
        self.code.push(if is_small { 0x6b } else { 0x69 });
        self.emit_modrm(Some(dst), 0, rm);
        if is_small {
            self.code.push(imm as u8);
        } else {
            self.code.extend_from_slice(&imm.to_le_bytes());
        }
    }

    pub fn emit_mul_r64_rm64(&mut self, dst: Reg, rm: RegMem) {
        self.emit_rex(true, false, Some(dst), rm);
        self.code.push(0x0f);
        self.code.push(0xaf);
        self.emit_modrm(Some(dst), 0, rm);
    }

    pub fn emit_inc_rm64(&mut self, dst: RegMem) {
        self.emit_rex(true, false, None, dst);
        self.code.push(0xff);
        self.emit_modrm(None, 0, dst);
    }

    pub fn emit_inc_rm32(&mut self, dst: RegMem) {
        self.emit_rex(false, false, None, dst);
        self.code.push(0xff);
        self.emit_modrm(None, 0, dst);
    }

    pub fn emit_inc_rm16(&mut self, dst: RegMem) {
        self.code.push(0x66);
        self.emit_rex(false, false, None, dst);
        self.code.push(0xff);
        self.emit_modrm(None, 0, dst);
    }

    pub fn emit_inc_rm8(&mut self, dst: RegMem) {
        self.emit_rex(false, true, None, dst);
        self.code.push(0xfe);
        self.emit_modrm(None, 0, dst);
    }

    pub fn emit_dec_rm64(&mut self, dst: RegMem) {
        self.emit_rex(true, false, None, dst);
        self.code.push(0xff);
        self.emit_modrm(None, 1, dst);
    }

    pub fn emit_dec_rm32(&mut self, dst: RegMem) {
        self.emit_rex(false, false, None, dst);
        self.code.push(0xff);
        self.emit_modrm(None, 1, dst);
    }

    pub fn emit_dec_rm16(&mut self, dst: RegMem) {
        self.code.push(0x66);
        self.emit_rex(false, false, None, dst);
        self.code.push(0xff);
        self.emit_modrm(None, 1, dst);
    }

    pub fn emit_dec_rm8(&mut self, dst: RegMem) {
        self.emit_rex(false, true, None, dst);
        self.code.push(0xfe);
        self.emit_modrm(None, 1, dst);
    }

    /// Automatically selects between the 64 bit or 32 bit immediate version.
    pub fn emit_mov_r64_i64(&mut self, reg: Reg, imm: i64) {
        let is_small = imm <= i32::MAX as i64 && imm >= i32::MIN as i64;
        let is_small_uns = imm >= 0 && imm <= u32::MAX as i64;
        self.emit_rex(!is_small_uns, false, None, RegMem::Reg(reg));
        if is_small || is_small_uns {
            self.code.push(0xc7);
            self.emit_modrm(None, 0, RegMem::Reg(reg));
            self.code.extend_from_slice(&(imm as i32).to_le_bytes());
        } else {
            self.code.push(0xb8 + reg.enc());
            self.code.extend_from_slice(&imm.to_le_bytes());
        }
    }

    pub fn emit_mov_rm64_i32(&mut self, rm: RegMem, imm: i32) {
        self.emit_rex(true, false, None, rm);
        self.code.push(0xc7);
        self.emit_modrm(None, 0, rm);
        self.code.extend_from_slice(&imm.to_le_bytes());
    }

    pub fn emit_mov_rm32_i32(&mut self, rm: RegMem, imm: i32) {
        self.emit_rex(false, false, None, rm);
        self.code.push(0xc7);
        self.emit_modrm(None, 0, rm);
        self.code.extend_from_slice(&imm.to_le_bytes());
    }

    pub fn emit_mov_rm16_i16(&mut self, rm: RegMem, imm: i16) {
        self.code.push(0x66);
        self.emit_rex(false, false, None, rm);
        self.code.push(0xc7);
        self.emit_modrm(None, 0, rm);
        self.code.extend_from_slice(&imm.to_le_bytes());
    }

    pub fn emit_mov_rm8_i8(&mut self, rm: RegMem, imm: i8) {
        self.emit_rex(false, true, None, rm);
        self.code.push(0xc6);
        self.emit_modrm(None, 0, rm);
        self.code.push(imm as u8);
    }

    pub fn emit_mov_r64_rm64(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(true, false, Some(dst), src);
        self.code.push(0x8b);
        self.emit_modrm(Some(dst), 0, src);
    }

    pub fn emit_mov_rm64_r64(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(true, false, Some(src), dst);
        self.code.push(0x89);
        self.emit_modrm(Some(src), 0, dst);
    }

    /// Zero extended load of a 32 bit memory location into a 64 bit register.
    pub fn emit_mov_r64_rm32(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(false, false, Some(dst), src);
        self.code.push(0x8b);
        self.emit_modrm(Some(dst), 0, src);
    }

    pub fn emit_mov_rm32_r32(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(false, false, Some(src), dst);
        self.code.push(0x89);
        self.emit_modrm(Some(src), 0, dst);
    }

    /// Zero extended load of a 16 bit memory location into a 64 bit register.
    pub fn emit_mov_r64_rm16(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(false, false, Some(dst), src);
        self.code.push(0x0f);
        self.code.push(0xb7);
        self.emit_modrm(Some(dst), 0, src);
    }

    pub fn emit_mov_rm16_r16(&mut self, dst: RegMem, src: Reg) {
        self.code.push(0x66);
        self.emit_rex(false, false, Some(src), dst);
        self.code.push(0x89);
        self.emit_modrm(Some(src), 0, dst);
    }

    /// Zero extended load of a 8 bit memory location into a 64 bit register.
    pub fn emit_mov_r64_rm8(&mut self, dst: Reg, src: RegMem) {
        self.emit_rex(false, false, Some(dst), src);
        self.code.push(0x0f);
        self.code.push(0xb6);
        self.emit_modrm(Some(dst), 0, src);
    }

    pub fn emit_mov_rm8_r8(&mut self, dst: RegMem, src: Reg) {
        self.emit_rex(false, true, Some(src), dst);
        self.code.push(0x88);
        self.emit_modrm(Some(src), 0, dst);
    }

    pub fn emit_lea(&mut self, dst: Reg, addr: RegMem) {
        self.emit_rex(true, false, Some(dst), addr);
        self.code.push(0x8d);
        self.emit_modrm(Some(dst), 0, addr);
    }

    pub fn emit_cmp_r64_rm64(&mut self, fst: Reg, snd: RegMem) {
        self.emit_rex(true, false, Some(fst), snd);
        self.code.push(0x3b);
        self.emit_modrm(Some(fst), 0, snd);
    }

    pub fn emit_cmp_rm64_i8(&mut self, rm: RegMem, imm: i8) {
        self.emit_rex(true, false, None, rm);
        self.code.push(0x83);
        self.emit_modrm(None, 7, rm);
        self.code.push(imm as u8);
    }

    pub fn emit_cmp_rm32_i8(&mut self, rm: RegMem, imm: i8) {
        self.emit_rex(false, false, None, rm);
        self.code.push(0x83);
        self.emit_modrm(None, 7, rm);
        self.code.push(imm as u8);
    }

    pub fn emit_cmp_rm16_i8(&mut self, rm: RegMem, imm: i8) {
        self.code.push(0x66);
        self.emit_rex(false, false, None, rm);
        self.code.push(0x83);
        self.emit_modrm(None, 7, rm);
        self.code.push(imm as u8);
    }

    pub fn emit_cmp_rm8_i8(&mut self, rm: RegMem, imm: i8) {
        self.emit_rex(false, true, None, rm);
        self.code.push(0x80);
        self.emit_modrm(None, 7, rm);
        self.code.push(imm as u8);
    }

    pub fn emit_test_rm8_r8(&mut self, fst: RegMem, snd: Reg) {
        self.emit_rex(false, true, Some(snd), fst);
        self.code.push(0x84);
        self.emit_modrm(Some(snd), 0, fst);
    }

    pub fn emit_jmp_rel8(&mut self, off: i8) {
        self.code.push(0xeb);
        self.code.push(off as u8);
    }

    pub fn emit_jcc_rel8(&mut self, pred: JmpPred, off: i8) {
        self.code.push(0x70 + pred as u8);
        self.code.push(off as u8);
    }

    pub fn emit_jcc_rel32(&mut self, pred: JmpPred, off: i32) {
        self.code.push(0x0f);
        self.code.push(0x80 + pred as u8);
        self.code.extend_from_slice(&off.to_le_bytes());
    }

    /// Arithmetic right shift by the specified constant.
    pub fn emit_sar_r64_i8(&mut self, dst: RegMem, shift: u8) {
        self.emit_rex(true, false, None, dst);
        self.code.push(0xc1);
        self.emit_modrm(None, 7, dst);
        self.code.push(shift);
    }

    pub fn emit_ret(&mut self) {
        self.code.push(0xc3);
    }

    pub fn emit_call_ind(&mut self, target: RegMem) {
        self.code.push(0xff);
        self.emit_modrm(None, 2, target);
    }
}
