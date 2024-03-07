//! LLVM JIT backend.

use inkwell::{
    attributes::{Attribute, AttributeLoc},
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
pub struct LlvmInterpreter<C: CellType> {
    program: Program<C>,
    min_accessed: isize,
    max_accessed: isize,
    opt: u32,
}

/// Function type of the generated JIT function.
type HpbfEntry<'a, C> = unsafe extern "C" fn(cxt: *mut Context<'a, C>, mem: *mut C);

/// Struct holding information needed during LLVM IR generation.
struct CodeGen<'cxt, 'int: 'cxt, C: CellType> {
    inp: &'int LlvmInterpreter<C>,
    context: &'cxt inkwell::context::Context,
    module: Module<'cxt>,
    builder: Builder<'cxt>,
    target_machine: TargetMachine,
    void_type: VoidType<'cxt>,
    int_type: IntType<'cxt>,
    intptr_type: IntType<'cxt>,
    ptr_type: PointerType<'cxt>,
    cxt_type: StructType<'cxt>,
}

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

    fn create_runtime_func_defs(
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
            self.void_type
                .fn_type(&[self.ptr_type.into(), self.int_type.into()], false),
            None,
        );
        self.apply_runtime_func_attributes(&runtime_output, true);
        (runtime_extend, runtime_input, runtime_output)
    }

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

    fn create_mov_func_def(
        &self,
        rt_extend: FunctionValue<'cxt>,
    ) -> Result<FunctionValue<'cxt>, BuilderError> {
        let mov = self.module.add_function(
            "mov",
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

    fn compile_block(
        &self,
        rt_input: FunctionValue<'cxt>,
        rt_output: FunctionValue<'cxt>,
        mov: FunctionValue<'cxt>,
        block: &Block<C>,
        func: FunctionValue<'cxt>,
        cxt_ptr: PointerValue<'cxt>,
        mut mem_ptr: PointerValue<'cxt>,
    ) -> Result<PointerValue<'cxt>, BuilderError> {
        for inst in &block.insts {
            match inst {
                Instr::Output { src } => {
                    let ptr = self.build_load_pointer(
                        mem_ptr,
                        self.intptr_type.const_int(*src as u64, false),
                        true,
                    )?;
                    let value = self.builder.build_load(self.int_type, ptr, "value")?;
                    self.builder
                        .build_call(rt_output, &[cxt_ptr.into(), value.into()], "")?;
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
                Instr::Loop { cond, block, .. } => {
                    let prev = self.builder.get_insert_block().unwrap();
                    let check = self.context.append_basic_block(func, "check");
                    let body = self.context.append_basic_block(func, "body");
                    let next = self.context.append_basic_block(func, "next");
                    self.builder.build_unconditional_branch(check)?;
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
                    let new_mem_ptr = self.compile_block(
                        rt_input,
                        rt_output,
                        mov,
                        block,
                        func,
                        cxt_ptr,
                        mem_ptr_next,
                    )?;
                    self.builder.build_unconditional_branch(check)?;
                    let body_end = self.builder.get_insert_block().unwrap();
                    mem_ptr_phi.add_incoming(&[(&mem_ptr, prev), (&new_mem_ptr, body_end)]);
                    self.builder.position_at_end(next);
                    mem_ptr = mem_ptr_next;
                }
                Instr::If { cond, block } => {
                    let prev = self.builder.get_insert_block().unwrap();
                    let body = self.context.append_basic_block(func, "body");
                    let next = self.context.append_basic_block(func, "next");
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
                        .compile_block(rt_input, rt_output, mov, block, func, cxt_ptr, mem_ptr)?;
                    self.builder.build_unconditional_branch(next)?;
                    let body_end = self.builder.get_insert_block().unwrap();
                    self.builder.position_at_end(next);
                    let mem_ptr_phi = self.builder.build_phi(self.ptr_type, "mem_ptr")?;
                    mem_ptr_phi.add_incoming(&[(&mem_ptr, prev), (&new_mem_ptr, body_end)]);
                    mem_ptr = mem_ptr_phi.as_basic_value().into_pointer_value();
                }
            }
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

    fn compile_program(
        &self,
        rt_input: FunctionValue<'cxt>,
        rt_output: FunctionValue<'cxt>,
        mov: FunctionValue<'cxt>,
    ) -> Result<(), BuilderError> {
        let func = self.module.add_function(
            "hpbf_entry",
            self.void_type.fn_type(&[self.ptr_type.into()], false),
            None,
        );
        let cxt_ptr = func.get_nth_param(0).unwrap().into_pointer_value();
        let entry = self.context.append_basic_block(func, "entry");
        self.builder.position_at_end(entry);
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
        self.compile_block(
            rt_input,
            rt_output,
            mov,
            &self.inp.program,
            func,
            cxt_ptr,
            mem_ptr,
        )?;
        self.builder.build_return(None)?;
        Ok(())
    }

    fn create(
        context: &'cxt inkwell::context::Context,
        inp: &'int LlvmInterpreter<C>,
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
            &[ptr_type.into(), intptr_type.into(), intptr_type.into()],
            false,
        );
        let code_gen = CodeGen {
            inp,
            context,
            module,
            builder,
            target_machine,
            void_type,
            int_type,
            intptr_type,
            ptr_type,
            cxt_type,
        };
        let (rt_extend, rt_input, rt_output) = code_gen.create_runtime_func_defs();
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
                "simplifycfg",
                "break-crit-edges",
                "loop-simplify",
                "mem2reg",
                "gvn",
                "loop-mssa(licm)",
                "instcombine",
                "reassociate",
                "sccp",
                "adce",
                "aggressive-instcombine",
                "simplifycfg",
            ];
            passes.join(",")
        } else {
            format!("default<O{}>", (inp.opt - 2).max(3))
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
    pub fn print_llvm_ir(&self) -> Result<String, Error> {
        let context = inkwell::context::Context::create();
        let module = CodeGen::create(&context, self)?;
        Ok(module.print_to_string().to_string())
    }

    fn enter_jit_code(&self, cxt: &mut Context<C>, module: Module) -> Result<(), Error> {
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
        unsafe {
            let func: JitFunction<HpbfEntry<C>> = execution_engine
                .get_function("hpbf_entry")
                .map_err(llvm_error)?;
            let cxt_ptr = cxt as *mut Context<C>;
            let mem_ptr = (*cxt_ptr).memory.current_ptr();
            func.call(cxt_ptr, mem_ptr);
        }
        Ok(())
    }

    /// Execute in the given context using the LLVM based JIT compiler.
    fn execute_in<'a>(&self, cxt: &mut Context<'a, C>) -> Result<(), Error> {
        cxt.memory
            .make_accessible(self.min_accessed, self.max_accessed);
        let context = inkwell::context::Context::create();
        let module = CodeGen::create(&context, self)?;
        self.enter_jit_code(cxt, module)
    }

    /// Execute in the given context using the LLVM based JIT compiler.
    fn execute_limited_in(&self, _cxt: &mut Context<C>, _budget: usize) -> Result<bool, Error> {
        todo!()
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

extern "C" fn hpbf_context_extend<C: CellType>(
    cxt: &mut Context<'static, C>,
    min: isize,
    max: isize,
) {
    cxt.memory.make_accessible(min, max);
}

extern "C" fn hpbf_context_input<C: CellType>(cxt: &mut Context<'static, C>) -> C {
    C::from_u8(cxt.input().unwrap_or(0))
}

extern "C" fn hpbf_context_output<C: CellType>(cxt: &mut Context<'static, u8>, value: C) {
    cxt.output(value.into_u8());
}

// executor_tests!(LlvmInterpreter);
// same_as_inplace_tests!(LlvmInterpreter);
