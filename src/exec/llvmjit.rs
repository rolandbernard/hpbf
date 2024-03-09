//! LLVM JIT backend.

use std::collections::HashMap;

use inkwell::{
    attributes::{Attribute, AttributeLoc},
    basic_block::BasicBlock,
    builder::{Builder, BuilderError},
    execution_engine::JitFunction,
    module::{Linkage, Module},
    passes::PassBuilderOptions,
    targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine},
    types::{IntType, PointerType, StructType, VoidType},
    values::{FunctionValue, IntValue, PointerValue},
    AddressSpace, IntPredicate, OptimizationLevel,
};

use crate::{
    ir::{self, Block, Instr, Program},
    runtime::Context,
    CellType, Error, ErrorKind,
};

use super::{Executable, Executor};

/// A LLVM backed JIT compiler. Builds LLVM IR from the internal brainfuck IR.
///
/// # Examples
/// ```
/// # use hpbf::{ir::{Program, Block, Instr}, Error, runtime::Context, exec::{Executor, Executable, LlvmInterpreter}};
/// # let mut buf = Vec::new();
/// # let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
/// # let code = "++++++[>+++++<-]>++[>++<-]++++[>++<-]>[.>]";
/// let exec = LlvmInterpreter::<u8>::create(code, 1)?;
/// exec.execute(&mut ctx)?;
/// # drop(ctx);
/// # assert_eq!(String::from_utf8(buf).unwrap(), "H");
/// # Ok::<(), Error>(())
/// ```
pub struct LlvmInterpreter<C: CellType> {
    program: Program<C>,
    min_accessed: isize,
    max_accessed: isize,
    opt: u32,
}

/// Function type of the generated JIT function.
type HpbfEntry<'a, C> = unsafe extern "C" fn(cxt: *mut Context<'a, C>) -> *mut C;

/// Struct holding information needed during LLVM IR generation.
struct CodeGen<'cxt, 'int: 'cxt, C: CellType> {
    inp: &'int LlvmInterpreter<C>,
    has_budget: bool,
    context: &'cxt inkwell::context::Context,
    module: Module<'cxt>,
    builder: Builder<'cxt>,
    target_machine: TargetMachine,
    void_type: VoidType<'cxt>,
    int_type: IntType<'cxt>,
    intptr_type: IntType<'cxt>,
    ptr_type: PointerType<'cxt>,
    cxt_type: StructType<'cxt>,
    blocks: HashMap<&'int Block<C>, FunctionValue<'cxt>>,
}

/// Generates LLVM values from the IR expressions.
struct LlvmCodeGenCalc<'a, 'cxt, 'int, C: CellType> {
    codegen: &'a CodeGen<'cxt, 'int, C>,
    mem_ptr: PointerValue<'cxt>,
}

/// Create an LLVM error with the given string.
fn llvm_error<S: ToString>(str: S) -> Error {
    Error {
        kind: ErrorKind::LlvmError,
        str: str.to_string(),
        position: 0,
    }
}

impl<'a, 'b: 'c, 'c, C: CellType> ir::CodeGen<C> for LlvmCodeGenCalc<'a, 'b, 'c, C> {
    type Output = IntValue<'c>;
    type Error = BuilderError;

    fn imm(&mut self, imm: C) -> Result<Self::Output, Self::Error> {
        Ok(self.codegen.int_type.const_int(imm.into_u64(), false))
    }

    fn mem(&mut self, var: isize) -> Result<Self::Output, Self::Error> {
        let ptr = self.codegen.build_load_pointer(
            self.mem_ptr,
            self.codegen.intptr_type.const_int(var as u64, false),
            true,
        )?;
        Ok(self
            .codegen
            .builder
            .build_load(self.codegen.int_type, ptr, "value")?
            .into_int_value())
    }

    fn add(&mut self, a: Self::Output, b: Self::Output) -> Result<Self::Output, Self::Error> {
        self.codegen.builder.build_int_add(a, b, "value")
    }

    fn sub(&mut self, a: Self::Output, b: Self::Output) -> Result<Self::Output, Self::Error> {
        self.codegen.builder.build_int_sub(a, b, "value")
    }

    fn mul(&mut self, a: Self::Output, b: Self::Output) -> Result<Self::Output, Self::Error> {
        self.codegen.builder.build_int_mul(a, b, "value")
    }
}

impl<'cxt, 'int: 'cxt, C: CellType> CodeGen<'cxt, 'int, C> {
    /// Apply the function attributes to the runtime functions. Runtime functions
    /// will always be marked cold, will always return, not capture the pointer, etc.
    fn apply_runtime_func_attributes(&self, func: &FunctionValue<'cxt>, read_none: bool) {
        let readnone_kind = Attribute::get_named_enum_kind_id("readnone");
        let nocapture_kind = Attribute::get_named_enum_kind_id("nocapture");
        let cold_kind = Attribute::get_named_enum_kind_id("cold");
        let memory_kind = Attribute::get_named_enum_kind_id("memory");
        let noalias_kind = Attribute::get_named_enum_kind_id("noalias");
        let willreturn_kind = Attribute::get_named_enum_kind_id("willreturn");
        let nosync_kind = Attribute::get_named_enum_kind_id("nosync");
        let nounwind_kind = Attribute::get_named_enum_kind_id("nounwind");
        if read_none {
            func.add_attribute(
                AttributeLoc::Param(0),
                self.context.create_enum_attribute(readnone_kind, 0),
            );
        }
        func.add_attribute(
            AttributeLoc::Param(0),
            self.context.create_enum_attribute(nocapture_kind, 0),
        );
        func.add_attribute(
            AttributeLoc::Param(0),
            self.context.create_enum_attribute(noalias_kind, 0),
        );
        func.add_attribute(
            AttributeLoc::Function,
            self.context.create_enum_attribute(cold_kind, 0),
        );
        func.add_attribute(
            AttributeLoc::Function,
            self.context.create_enum_attribute(willreturn_kind, 0),
        );
        func.add_attribute(
            AttributeLoc::Function,
            self.context.create_enum_attribute(nosync_kind, 0),
        );
        func.add_attribute(
            AttributeLoc::Function,
            self.context.create_enum_attribute(nounwind_kind, 0),
        );
        func.add_attribute(
            AttributeLoc::Function,
            self.context
                .create_enum_attribute(memory_kind, if read_none { 0xc } else { 0xf }),
        );
    }

    /// Create the function declaration for the three runtime functions.
    fn create_runtime_func_decl(
        &self,
    ) -> (
        FunctionValue<'cxt>,
        FunctionValue<'cxt>,
        FunctionValue<'cxt>,
    ) {
        let runtime_extend = self.module.add_function(
            "hpbf_context_extend",
            self.void_type.fn_type(
                &[
                    self.ptr_type.into(),
                    self.intptr_type.into(),
                    self.intptr_type.into(),
                ],
                false,
            ),
            None,
        );
        self.apply_runtime_func_attributes(&runtime_extend, false);
        let runtime_input = self.module.add_function(
            "hpbf_context_input",
            self.int_type.fn_type(&[self.ptr_type.into()], false),
            None,
        );
        self.apply_runtime_func_attributes(&runtime_input, true);
        let runtime_output = self.module.add_function(
            "hpbf_context_output",
            self.context
                .bool_type()
                .fn_type(&[self.ptr_type.into(), self.int_type.into()], false),
            None,
        );
        self.apply_runtime_func_attributes(&runtime_output, true);
        (runtime_extend, runtime_input, runtime_output)
    }

    /// Build a pointer to an offset from the base pointer. This is the only use of
    /// the getElementPointer instruction in this backend (excluding struct GEPs).
    fn build_load_pointer(
        &self,
        base: PointerValue<'cxt>,
        offset: IntValue<'cxt>,
        in_bounds: bool,
    ) -> Result<PointerValue<'cxt>, BuilderError> {
        unsafe {
            if in_bounds {
                self.builder
                    .build_in_bounds_gep(self.int_type, base, &[offset], "mem_offset")
            } else {
                self.builder
                    .build_gep(self.int_type, base, &[offset], "mem_offset")
            }
        }
    }

    /// Create the definition of mov function. This function moves the memory pointer,
    /// performs bounds checking and returns the new pointer.
    fn create_mov_func_def(
        &self,
        rt_extend: FunctionValue<'cxt>,
    ) -> Result<FunctionValue<'cxt>, BuilderError> {
        let mov = self.module.add_function(
            "hpbf_mov",
            self.ptr_type.fn_type(
                &[
                    self.ptr_type.into(),
                    self.ptr_type.into(),
                    self.intptr_type.into(),
                    self.intptr_type.into(),
                ],
                false,
            ),
            Some(Linkage::Private),
        );
        let fast_cc = Attribute::get_named_enum_kind_id("fastcc");
        mov.set_call_conventions(fast_cc);
        let cxt_ptr = mov.get_nth_param(0).unwrap().into_pointer_value();
        let mem_ptr = mov.get_nth_param(1).unwrap().into_pointer_value();
        let shift = mov.get_nth_param(2).unwrap().into_int_value();
        let probe = mov.get_nth_param(3).unwrap().into_int_value();
        let entry = self.context.append_basic_block(mov, "entry");
        let resize = self.context.append_basic_block(mov, "resize");
        let exit = self.context.append_basic_block(mov, "exit");
        self.builder.position_at_end(entry);
        let new_mem_ptr = self.build_load_pointer(mem_ptr, shift, false)?;
        let mem_base_ptr =
            self.builder
                .build_struct_gep(self.cxt_type, cxt_ptr, 0, "mem_base_ptr")?;
        let mem_base = self
            .builder
            .build_load(self.ptr_type, mem_base_ptr, "mem_base")?
            .into_pointer_value();
        let mem_size_ptr =
            self.builder
                .build_struct_gep(self.cxt_type, cxt_ptr, 1, "mem_size_ptr")?;
        let mem_size = self
            .builder
            .build_load(self.intptr_type, mem_size_ptr, "mem_size")?
            .into_int_value();
        let mem_probe = self.build_load_pointer(new_mem_ptr, probe, false)?;
        let mem_diff =
            self.builder
                .build_ptr_diff(self.int_type, mem_probe, mem_base, "mem_diff")?;
        let is_less =
            self.builder
                .build_int_compare(IntPredicate::ULT, mem_diff, mem_size, "mem_ok")?;
        self.builder
            .build_conditional_branch(is_less, exit, resize)?;
        self.builder.position_at_end(resize);
        let mem_off =
            self.builder
                .build_ptr_diff(self.int_type, new_mem_ptr, mem_base, "mem_off")?;
        let mem_off_ptr =
            self.builder
                .build_struct_gep(self.cxt_type, cxt_ptr, 2, "mem_off_ptr")?;
        self.builder.build_store(mem_off_ptr, mem_off)?;
        let probe_p1 =
            self.builder
                .build_int_add(probe, self.intptr_type.const_int(1, false), "probe_p1")?;
        self.builder.build_call(
            rt_extend,
            &[cxt_ptr.into(), probe.into(), probe_p1.into()],
            "",
        )?;
        let mem_base = self
            .builder
            .build_load(self.ptr_type, mem_base_ptr, "mem_base")?
            .into_pointer_value();
        let mem_off = self
            .builder
            .build_load(self.intptr_type, mem_off_ptr, "mem_off")?
            .into_int_value();
        let resized_mem_ptr = self.build_load_pointer(mem_base, mem_off, true)?;
        self.builder.build_unconditional_branch(exit)?;
        self.builder.position_at_end(exit);
        let mem_ptr = self.builder.build_phi(self.ptr_type, "mem_ptr")?;
        mem_ptr.add_incoming(&[(&new_mem_ptr, entry), (&resized_mem_ptr, resize)]);
        self.builder.build_return(Some(&mem_ptr.as_basic_value()))?;
        Ok(mov)
    }

    /// Compile the given IR block. Returns the LLVM value for the new memory pointer.
    fn compile_block(
        &mut self,
        rt_input: FunctionValue<'cxt>,
        rt_output: FunctionValue<'cxt>,
        mov: FunctionValue<'cxt>,
        block: &'int Block<C>,
        func: FunctionValue<'cxt>,
        term: BasicBlock<'cxt>,
        cxt_ptr: PointerValue<'cxt>,
        mut mem_ptr: PointerValue<'cxt>,
    ) -> Result<PointerValue<'cxt>, BuilderError> {
        for inst in &block.insts {
            match inst {
                Instr::Output { src } => {
                    let next = self.context.append_basic_block(func, "next");
                    let ptr = self.build_load_pointer(
                        mem_ptr,
                        self.intptr_type.const_int(*src as u64, false),
                        true,
                    )?;
                    let value = self.builder.build_load(self.int_type, ptr, "value")?;
                    let interrupted = self
                        .builder
                        .build_call(rt_output, &[cxt_ptr.into(), value.into()], "interrupted")?
                        .try_as_basic_value()
                        .unwrap_left()
                        .into_int_value();
                    self.builder
                        .build_conditional_branch(interrupted, term, next)?;
                    self.builder.position_at_end(next);
                }
                Instr::Input { dst } => {
                    let value = self
                        .builder
                        .build_call(rt_input, &[cxt_ptr.into()], "value")?
                        .try_as_basic_value()
                        .unwrap_left();
                    let ptr = self.build_load_pointer(
                        mem_ptr,
                        self.intptr_type.const_int(*dst as u64, false),
                        true,
                    )?;
                    self.builder.build_store(ptr, value)?;
                }
                Instr::Calc { calcs } => {
                    let mut codegen = LlvmCodeGenCalc {
                        codegen: self,
                        mem_ptr,
                    };
                    let mut values = Vec::new();
                    for (var, calc) in calcs {
                        values.push((*var, calc.codegen(&mut codegen, |_| 0)?));
                    }
                    for (var, value) in values {
                        let ptr = self.build_load_pointer(
                            mem_ptr,
                            self.intptr_type.const_int(var as u64, false),
                            true,
                        )?;
                        self.builder.build_store(ptr, value)?;
                    }
                }
                Instr::Loop { cond, block, once } => {
                    let prev = self.builder.get_insert_block().unwrap();
                    let check = self.context.append_basic_block(func, "check");
                    let body = self.context.append_basic_block(func, "body");
                    let next = self.context.append_basic_block(func, "next");
                    let block_func = self.create_block_func_def(rt_input, rt_output, mov, block)?;
                    self.builder.position_at_end(prev);
                    if *once {
                        mem_ptr = self
                            .builder
                            .build_call(block_func, &[cxt_ptr.into(), mem_ptr.into()], "mem_ptr")?
                            .try_as_basic_value()
                            .unwrap_left()
                            .into_pointer_value();
                        let ptr_int = self.builder.build_ptr_to_int(
                            mem_ptr,
                            self.intptr_type,
                            "mem_ptr_int",
                        )?;
                        let interrupted = self.builder.build_int_compare(
                            IntPredicate::EQ,
                            ptr_int,
                            self.intptr_type.const_zero(),
                            "interrupted",
                        )?;
                        self.builder
                            .build_conditional_branch(interrupted, term, check)?;
                    } else {
                        self.builder.build_unconditional_branch(check)?;
                    }
                    self.builder.position_at_end(check);
                    let mem_ptr_phi = self.builder.build_phi(self.ptr_type, "mem_ptr")?;
                    let mem_ptr_next = mem_ptr_phi.as_basic_value().into_pointer_value();
                    let ptr = self.build_load_pointer(
                        mem_ptr_next,
                        self.intptr_type.const_int(*cond as u64, false),
                        true,
                    )?;
                    let value = self
                        .builder
                        .build_load(self.int_type, ptr, "value")?
                        .into_int_value();
                    let is_zero = self.builder.build_int_compare(
                        IntPredicate::EQ,
                        value,
                        self.int_type.const_zero(),
                        "check",
                    )?;
                    self.builder.build_conditional_branch(is_zero, next, body)?;
                    self.builder.position_at_end(body);
                    let new_mem_ptr = self
                        .builder
                        .build_call(
                            block_func,
                            &[cxt_ptr.into(), mem_ptr_next.into()],
                            "new_mem_ptr",
                        )?
                        .try_as_basic_value()
                        .unwrap_left()
                        .into_pointer_value();
                    let ptr_int = self.builder.build_ptr_to_int(
                        new_mem_ptr,
                        self.intptr_type,
                        "mem_ptr_int",
                    )?;
                    let interrupted = self.builder.build_int_compare(
                        IntPredicate::EQ,
                        ptr_int,
                        self.intptr_type.const_zero(),
                        "interrupted",
                    )?;
                    self.builder
                        .build_conditional_branch(interrupted, term, check)?;
                    let body_end = self.builder.get_insert_block().unwrap();
                    mem_ptr_phi.add_incoming(&[(&mem_ptr, prev), (&new_mem_ptr, body_end)]);
                    self.builder.position_at_end(next);
                    mem_ptr = mem_ptr_next;
                }
                Instr::If { cond, block } => {
                    let prev = self.builder.get_insert_block().unwrap();
                    let body = self.context.append_basic_block(func, "body");
                    let next = self.context.append_basic_block(func, "next");
                    let block_func = self.create_block_func_def(rt_input, rt_output, mov, block)?;
                    self.builder.position_at_end(prev);
                    let ptr = self.build_load_pointer(
                        mem_ptr,
                        self.intptr_type.const_int(*cond as u64, false),
                        true,
                    )?;
                    let value = self
                        .builder
                        .build_load(self.int_type, ptr, "value")?
                        .into_int_value();
                    let is_zero = self.builder.build_int_compare(
                        IntPredicate::EQ,
                        value,
                        self.int_type.const_zero(),
                        "check",
                    )?;
                    self.builder.build_conditional_branch(is_zero, next, body)?;
                    self.builder.position_at_end(body);
                    let new_mem_ptr = self
                        .builder
                        .build_call(block_func, &[cxt_ptr.into(), mem_ptr.into()], "new_mem_ptr")?
                        .try_as_basic_value()
                        .unwrap_left()
                        .into_pointer_value();
                    let ptr_int = self.builder.build_ptr_to_int(
                        new_mem_ptr,
                        self.intptr_type,
                        "mem_ptr_int",
                    )?;
                    let interrupted = self.builder.build_int_compare(
                        IntPredicate::EQ,
                        ptr_int,
                        self.intptr_type.const_zero(),
                        "interrupted",
                    )?;
                    self.builder
                        .build_conditional_branch(interrupted, term, next)?;
                    let body_end = self.builder.get_insert_block().unwrap();
                    self.builder.position_at_end(next);
                    let mem_ptr_phi = self.builder.build_phi(self.ptr_type, "mem_ptr")?;
                    mem_ptr_phi.add_incoming(&[(&mem_ptr, prev), (&new_mem_ptr, body_end)]);
                    mem_ptr = mem_ptr_phi.as_basic_value().into_pointer_value();
                }
            }
        }
        if self.has_budget {
            let next = self.context.append_basic_block(func, "next");
            let budget_ptr =
                self.builder
                    .build_struct_gep(self.cxt_type, cxt_ptr, 3, "budget_ptr")?;
            let budget = self
                .builder
                .build_load(self.intptr_type, budget_ptr, "budget")?
                .into_int_value();
            let budget = self.builder.build_int_sub(
                budget,
                self.intptr_type.const_int(1, false),
                "budget",
            )?;
            self.builder.build_store(budget_ptr, budget)?;
            let is_over = self.builder.build_int_compare(
                IntPredicate::SLE,
                budget,
                self.intptr_type.const_zero(),
                "is_over",
            )?;
            self.builder.build_conditional_branch(is_over, term, next)?;
            self.builder.position_at_end(next);
        }
        if block.shift != 0 {
            mem_ptr = self
                .builder
                .build_call(
                    mov,
                    &[
                        cxt_ptr.into(),
                        mem_ptr.into(),
                        self.intptr_type.const_int(block.shift as u64, true).into(),
                        self.intptr_type
                            .const_int(
                                if block.shift < 0 {
                                    self.inp.min_accessed as u64
                                } else {
                                    self.inp.max_accessed as u64
                                },
                                true,
                            )
                            .into(),
                    ],
                    "mem_ptr",
                )?
                .try_as_basic_value()
                .unwrap_left()
                .into_pointer_value();
        }
        Ok(mem_ptr)
    }

    /// Create the function definition for the given block. All blocks are compiled
    /// to functions that take the context and returns the new memory pointer.
    fn create_block_func_def(
        &mut self,
        rt_input: FunctionValue<'cxt>,
        rt_output: FunctionValue<'cxt>,
        mov: FunctionValue<'cxt>,
        block: &'int Block<C>,
    ) -> Result<FunctionValue<'cxt>, BuilderError> {
        if self.blocks.contains_key(block) {
            return Ok(self.blocks[block]);
        }
        let func = self.module.add_function(
            "hpbf_block",
            self.ptr_type
                .fn_type(&[self.ptr_type.into(), self.ptr_type.into()], false),
            Some(Linkage::Private),
        );
        let fast_cc = Attribute::get_named_enum_kind_id("fastcc");
        func.set_call_conventions(fast_cc);
        let cxt_ptr = func.get_nth_param(0).unwrap().into_pointer_value();
        let mem_ptr = func.get_nth_param(1).unwrap().into_pointer_value();
        let body = self.context.append_basic_block(func, "body");
        let term = self.context.append_basic_block(func, "term");
        let exit = self.context.append_basic_block(func, "exit");
        self.builder.position_at_end(body);
        let mem_ptr = self.compile_block(
            rt_input, rt_output, mov, block, func, term, cxt_ptr, mem_ptr,
        )?;
        self.builder.build_unconditional_branch(exit)?;
        let prev = self.builder.get_insert_block().unwrap();
        self.builder.position_at_end(exit);
        let mem_ptr_phi = self.builder.build_phi(self.ptr_type, "new_ptr")?;
        mem_ptr_phi.add_incoming(&[(&mem_ptr, prev), (&self.ptr_type.const_null(), term)]);
        self.builder.position_at_end(term);
        self.builder.build_unconditional_branch(exit)?;
        self.builder.position_at_end(exit);
        self.builder
            .build_return(Some(&mem_ptr_phi.as_basic_value()))?;
        self.blocks.insert(block, func);
        Ok(func)
    }

    /// Compile the complete input program and define the entry function. The entry
    /// function takes the context pointer as input and returns either the new
    /// memory pointer or null if the program has been interrupted.
    fn compile_program(
        &mut self,
        rt_input: FunctionValue<'cxt>,
        rt_output: FunctionValue<'cxt>,
        mov: FunctionValue<'cxt>,
    ) -> Result<(), BuilderError> {
        let func = self.module.add_function(
            "hpbf_entry",
            self.ptr_type.fn_type(&[self.ptr_type.into()], false),
            None,
        );
        let cxt_ptr = func.get_nth_param(0).unwrap().into_pointer_value();
        let entry_func = self.create_block_func_def(rt_input, rt_output, mov, &self.inp.program)?;
        let body = self.context.append_basic_block(func, "body");
        self.builder.position_at_end(body);
        let mem_base_ptr =
            self.builder
                .build_struct_gep(self.cxt_type, cxt_ptr, 0, "mem_base_ptr")?;
        let mem_base = self
            .builder
            .build_load(self.ptr_type, mem_base_ptr, "mem_base")?
            .into_pointer_value();
        let mem_off_ptr =
            self.builder
                .build_struct_gep(self.cxt_type, cxt_ptr, 2, "mem_off_ptr")?;
        let mem_off = self
            .builder
            .build_load(self.intptr_type, mem_off_ptr, "mem_off")?
            .into_int_value();
        let mem_ptr = self.build_load_pointer(mem_base, mem_off, true)?;
        let mem_ptr = self
            .builder
            .build_call(entry_func, &[cxt_ptr.into(), mem_ptr.into()], "mem_ptr")?
            .try_as_basic_value()
            .unwrap_left();
        self.builder.build_return(Some(&mem_ptr))?;
        Ok(())
    }

    /// Compile the given bytecode program to an LLVM module and perform optimizations.
    fn create(
        context: &'cxt inkwell::context::Context,
        inp: &'int LlvmInterpreter<C>,
        has_budget: bool,
    ) -> Result<Module<'cxt>, Error> {
        Target::initialize_native(&InitializationConfig::default()).map_err(llvm_error)?;
        let triple = TargetMachine::get_default_triple();
        let target = Target::from_triple(&triple).map_err(llvm_error)?;
        let target_machine = target
            .create_target_machine(
                &triple,
                TargetMachine::get_host_cpu_name().to_str().unwrap(),
                TargetMachine::get_host_cpu_features().to_str().unwrap(),
                OptimizationLevel::None,
                RelocMode::Static,
                CodeModel::JITDefault,
            )
            .ok_or(llvm_error("failed to create target machine"))?;
        let target_data = target_machine.get_target_data();
        let module = context.create_module("hpbf");
        let builder = context.create_builder();
        module.set_triple(&triple);
        module.set_data_layout(&target_data.get_data_layout());
        let int_type = context.custom_width_int_type(C::BITS);
        let intptr_type = context.ptr_sized_int_type(&target_data, None);
        let void_type = context.void_type();
        let ptr_type = int_type.ptr_type(AddressSpace::default());
        let cxt_type = context.struct_type(
            &[
                ptr_type.into(),
                intptr_type.into(),
                intptr_type.into(),
                intptr_type.into(),
            ],
            false,
        );
        let mut code_gen = CodeGen {
            inp,
            has_budget,
            context,
            module,
            builder,
            target_machine,
            void_type,
            int_type,
            intptr_type,
            ptr_type,
            cxt_type,
            blocks: HashMap::new(),
        };
        let (rt_extend, rt_input, rt_output) = code_gen.create_runtime_func_decl();
        let mov = code_gen
            .create_mov_func_def(rt_extend)
            .map_err(llvm_error)?;
        code_gen
            .compile_program(rt_input, rt_output, mov)
            .map_err(llvm_error)?;
        #[cfg(debug_assertions)]
        code_gen.module.verify().map_err(llvm_error)?;
        let passes = if inp.opt == 0 {
            "default<O0>".to_owned()
        } else if inp.opt <= 2 {
            let passes = [
                "module(",
                "cgscc(",
                "inline,",
                "function(",
                "sccp,",
                "gvn,",
                "instcombine",
                ")))",
            ];
            passes.join("")
        } else if inp.opt <= 3 {
            let passes = [
                "module(",
                "cgscc(",
                "inline,",
                "function(",
                "simplifycfg,",
                "break-crit-edges,",
                "loop-simplify,",
                "mem2reg,",
                "reassociate,",
                "sccp,",
                "gvn,",
                "loop-mssa(licm),",
                "instcombine,",
                "aggressive-instcombine,",
                "adce,",
                "simplifycfg,",
                "dse",
                ")))",
            ];
            passes.join("")
        } else {
            format!("default<O{}>", (inp.opt - 3).max(3))
        };
        code_gen
            .module
            .run_passes(
                &passes,
                &code_gen.target_machine,
                PassBuilderOptions::create(),
            )
            .map_err(llvm_error)?;
        Ok(code_gen.module)
    }
}

impl<C: CellType> LlvmInterpreter<C> {
    /// Print the LLVM IR to a string and return that.
    pub fn print_llvm_ir(&self, limit: bool) -> Result<String, Error> {
        let context = inkwell::context::Context::create();
        let module = CodeGen::create(&context, self, limit)?;
        Ok(module.print_to_string().to_string())
    }

    /// JIT compile the LLVM module and enter with the entry function. Returns true
    /// if the program finished normally, and false if it was interrupted.
    fn enter_jit_code(&self, cxt: &mut Context<C>, module: Module) -> Result<bool, Error> {
        let opt_level = match self.opt {
            0 => OptimizationLevel::None,
            1 => OptimizationLevel::Less,
            2 => OptimizationLevel::Default,
            _ => OptimizationLevel::Aggressive,
        };
        let execution_engine = module
            .create_jit_execution_engine(opt_level)
            .map_err(llvm_error)?;
        if let Some(func) = module.get_function("hpbf_context_extend") {
            execution_engine.add_global_mapping(&func, hpbf_context_extend::<C> as usize);
        }
        if let Some(func) = module.get_function("hpbf_context_input") {
            execution_engine.add_global_mapping(&func, hpbf_context_input::<C> as usize);
        }
        if let Some(func) = module.get_function("hpbf_context_output") {
            execution_engine.add_global_mapping(&func, hpbf_context_output::<C> as usize);
        }
        cxt.memory
            .make_accessible(self.min_accessed, self.max_accessed + 1);
        let ret_mem = unsafe {
            let func: JitFunction<HpbfEntry<C>> = execution_engine
                .get_function("hpbf_entry")
                .map_err(llvm_error)?;
            let cxt_ptr = cxt as *mut Context<C>;
            func.call(cxt_ptr)
        };
        Ok(!ret_mem.is_null())
    }

    /// Execute in the given context using the LLVM based JIT compiler.
    fn execute_in<'a>(&self, cxt: &mut Context<'a, C>) -> Result<(), Error> {
        let context = inkwell::context::Context::create();
        let module = CodeGen::create(&context, self, false)?;
        self.enter_jit_code(cxt, module).map(|_| ())
    }

    /// Execute in the given context using the LLVM based JIT compiler.
    fn execute_limited_in(&self, cxt: &mut Context<C>, budget: usize) -> Result<bool, Error> {
        let context = inkwell::context::Context::create();
        let module = CodeGen::create(&context, self, true)?;
        cxt.budget = budget;
        self.enter_jit_code(cxt, module)
    }
}

impl<'p, C: CellType> Executor<'p, C> for LlvmInterpreter<C> {
    fn create(code: &str, opt: u32) -> Result<Self, Error> {
        let mut program = Program::<C>::parse(code)?;
        program = program.optimize(opt);
        let (min_accessed, max_accessed) = program.compute_min_max_accessed();
        Ok(LlvmInterpreter {
            program,
            opt,
            min_accessed,
            max_accessed,
        })
    }
}

impl<C: CellType> Executable<C> for LlvmInterpreter<C> {
    fn execute(&self, context: &mut Context<C>) -> Result<(), Error> {
        self.execute_in(context)
    }

    fn execute_limited(&self, context: &mut Context<C>, instr: usize) -> Result<bool, Error> {
        self.execute_limited_in(context, instr)
    }
}

/// Runtime function. Extends the memory buffer and moves the offset to make the range
/// from `min` (inclusive) to `max` (exclusive) accessible.
extern "C" fn hpbf_context_extend<C: CellType>(
    cxt: &mut Context<'static, C>,
    min: isize,
    max: isize,
) {
    cxt.memory.make_accessible(min, max);
}

/// Runtime function. Get a value form the input, or zero in case the input closed.
extern "C" fn hpbf_context_input<C: CellType>(cxt: &mut Context<'static, C>) -> C {
    C::from_u8(cxt.input().unwrap_or(0))
}

/// Runtime function. Print the given value to the output and return true if the output closed.
extern "C" fn hpbf_context_output<C: CellType>(cxt: &mut Context<'static, u8>, value: C) -> bool {
    cxt.output(value.into_u8()).is_none()
}

executor_tests!(LlvmInterpreter);
same_as_inplace_tests!(LlvmInterpreter);
