//! LLVM JIT backend.

use inkwell::{
    attributes::{Attribute, AttributeLoc},
    builder::Builder,
    execution_engine::JitFunction,
    module::Module,
    passes::PassBuilderOptions,
    support::LLVMString,
    targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetData, TargetMachine},
    types::{IntType, PointerType, VoidType},
    values::FunctionValue,
    AddressSpace, OptimizationLevel,
};

use crate::{ir::Program, runtime::Context, CellType, Error, ErrorKind};

use super::{Executable, Executor};

/// A LLVM backed JIT compiler. Builds LLVM IR from the internal brainfuck IR.
pub struct LlvmInterpreter<C: CellType> {
    program: Program<C>,
    opt: u32,
}

/// Function type of the generated JIT function.
type HpbfEntry<'a, C> = unsafe extern "C" fn(cxt: *mut Context<'a, C>, mem: *mut C);

/// Struct holding information needed during LLVM IR generation.
struct CodeGen<'cxt> {
    context: &'cxt inkwell::context::Context,
    module: Module<'cxt>,
    builder: Builder<'cxt>,
    target_data: TargetData,
    target_machine: TargetMachine,
    void_type: VoidType<'cxt>,
    int_type: IntType<'cxt>,
    intptr_type: IntType<'cxt>,
    ptr_type: PointerType<'cxt>,
}

/// Create an LLVM error with the given string.
fn llvm_error<S: ToString>(str: S) -> Error {
    Error {
        kind: ErrorKind::LlvmError,
        str: str.to_string(),
        position: 0,
    }
}

impl<'cxt> CodeGen<'cxt> {
    fn apply_runtime_func_attributes(&self, func: &FunctionValue, read_none: bool) {
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

    fn create_runtime_func_defs(&self) -> (FunctionValue, FunctionValue, FunctionValue) {
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

    fn create_mov_func_defs(&self) -> (FunctionValue, FunctionValue, FunctionValue, FunctionValue) {
        todo!()
    }

    fn compile_program<C: CellType>(
        &self,
        program: &Program<C>,
        rt_extend: FunctionValue,
        rt_input: FunctionValue,
        rt_output: FunctionValue,
        mvl: FunctionValue,
        mvr: FunctionValue,
        scl: FunctionValue,
        scr: FunctionValue,
    ) -> Result<(), LLVMString> {
        todo!()
    }

    fn create<C: CellType>(
        context: &'cxt inkwell::context::Context,
        program: &Program<C>,
        opt: u32,
    ) -> Result<Self, Error> {
        let opt_level = match opt {
            0 => OptimizationLevel::None,
            1 => OptimizationLevel::Less,
            2 => OptimizationLevel::Default,
            _ => OptimizationLevel::Aggressive,
        };
        Target::initialize_native(&InitializationConfig::default()).map_err(llvm_error)?;
        let triple = TargetMachine::get_default_triple();
        let target = Target::from_triple(&triple).map_err(llvm_error)?;
        let target_machine = target
            .create_target_machine(
                &triple,
                TargetMachine::get_host_cpu_name().to_str().unwrap(),
                TargetMachine::get_host_cpu_features().to_str().unwrap(),
                opt_level,
                RelocMode::PIC,
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
        let code_gen = CodeGen {
            context,
            module,
            builder,
            target_data,
            target_machine,
            void_type,
            int_type,
            intptr_type,
            ptr_type,
        };
        let (rt_extend, rt_input, rt_output) = code_gen.create_runtime_func_defs();
        let (mvl, mvr, scl, scr) = code_gen.create_mov_func_defs();
        code_gen
            .compile_program(program, rt_extend, rt_input, rt_output, mvl, mvr, scl, scr)
            .map_err(llvm_error)?;
        let passes = if opt == 0 {
            "default<O0>".to_owned()
        } else if opt == 1 {
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
            format!("default<O{}>", (opt - 1).max(3))
        };
        code_gen
            .module
            .run_passes(
                &passes,
                &code_gen.target_machine,
                PassBuilderOptions::create(),
            )
            .map_err(llvm_error)?;
        Ok(code_gen)
    }
}

impl<C: CellType> LlvmInterpreter<C> {
    /// Execute in the given context using the LLVM based JIT compiler.
    fn execute_in<'a>(&self, cxt: &mut Context<'a, C>) -> Result<(), Error> {
        let opt_level = match self.opt {
            0 => OptimizationLevel::None,
            1 => OptimizationLevel::Less,
            2 => OptimizationLevel::Default,
            _ => OptimizationLevel::Aggressive,
        };
        let context = inkwell::context::Context::create();
        let code_gen = CodeGen::create(&context, &self.program, self.opt)?;
        let execution_engine = code_gen
            .module
            .create_jit_execution_engine(opt_level)
            .map_err(|err| Error {
                kind: ErrorKind::LlvmError,
                str: err.to_string(),
                position: 0,
            })?;
        if let Some(func) = code_gen.module.get_function("hpbf_context_extend") {
            execution_engine.add_global_mapping(&func, hpbf_context_extend::<C> as usize);
        }
        if let Some(func) = code_gen.module.get_function("hpbf_context_input") {
            execution_engine.add_global_mapping(&func, hpbf_context_input::<C> as usize);
        }
        if let Some(func) = code_gen.module.get_function("hpbf_context_output") {
            execution_engine.add_global_mapping(&func, hpbf_context_output::<C> as usize);
        }
        unsafe {
            let func: JitFunction<HpbfEntry<'a, C>> = execution_engine
                .get_function("hpbf_program_entry")
                .map_err(|err| Error {
                    kind: ErrorKind::LlvmError,
                    str: err.to_string(),
                    position: 0,
                })?;
            let cxt_ptr = cxt as *mut Context<'a, C>;
            let mem_ptr = (*cxt_ptr).memory.current_ptr();
            func.call(cxt_ptr, mem_ptr);
        }
        Ok(())
    }

    /// Execute in the given context using the LLVM based JIT compiler.
    fn execute_limited_in(&self, cxt: &mut Context<C>, budget: usize) -> Result<bool, Error> {
        todo!()
    }
}

impl<'p, C: CellType> Executor<'p, C> for LlvmInterpreter<C> {
    fn create(code: &str, opt: u32) -> Result<Self, Error> {
        let mut program = Program::<C>::parse(code)?;
        program = program.optimize(opt);
        Ok(LlvmInterpreter { program, opt })
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
