use inkwell::{
    basic_block::BasicBlock,
    builder::Builder,
    execution_engine::JitFunction,
    module::Module,
    passes::PassBuilderOptions,
    targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine},
    values::PointerValue,
    AddressSpace, OptimizationLevel,
};

use crate::{Block, CellType, Context};

type HpbfEntry<'a, C> = unsafe extern "C" fn(cxt: *mut Context<'a, C>);

struct CodeGen<'cxt> {
    context: &'cxt inkwell::context::Context,
    module: Module<'cxt>,
    builder: Builder<'cxt>,
}

impl<'cxt> CodeGen<'cxt> {
    fn compile_block<C: CellType>(
        &self,
        block: &Block<C>,
        basic_block: BasicBlock<'cxt>,
        cxt_ptr: PointerValue,
        mem_ptr: PointerValue,
        mem_low: PointerValue,
        mem_high: PointerValue,
    ) -> Result<(), String> {
        todo!();
        Ok(())
    }

    fn compile_program<'a, C: CellType>(&self, program: &Block<C>) -> Result<(), String> {
        let int_type = self.context.custom_width_int_type(C::BITS);
        let void_type = self.context.void_type();
        let ptr_type = int_type.ptr_type(AddressSpace::default());
        let function = self.module.add_function(
            "hpbf_entry",
            void_type.fn_type(&[ptr_type.into()], false),
            None,
        );
        let basic_block = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(basic_block);
        let context_ptr = function.get_nth_param(0).unwrap().into_pointer_value();
        let cxt_struct_type = self
            .context
            .struct_type(&[ptr_type.into(), ptr_type.into(), ptr_type.into()], false);
        self.compile_block(
            program,
            basic_block,
            context_ptr,
            self.builder
                .build_struct_gep(cxt_struct_type, context_ptr, 2, "mem_ptr")
                .map_err(|err| err.to_string())?,
            self.builder
                .build_struct_gep(cxt_struct_type, context_ptr, 0, "mem_low")
                .map_err(|err| err.to_string())?,
            self.builder
                .build_struct_gep(cxt_struct_type, context_ptr, 1, "mem_high")
                .map_err(|err| err.to_string())?,
        )
    }
}

impl<'a, C: CellType> Context<'a, C> {
    pub fn jit_execute(&mut self, opt: u32, program: &Block<C>) -> Result<(), String> {
        let opt_level = match opt {
            1 => OptimizationLevel::Less,
            2 => OptimizationLevel::Default,
            3 => OptimizationLevel::Aggressive,
            _ => OptimizationLevel::None,
        };
        Target::initialize_native(&InitializationConfig::default())?;
        let triple = TargetMachine::get_default_triple();
        let target = Target::from_triple(&triple).map_err(|err| err.to_string())?;
        let target_machine = target
            .create_target_machine(
                &triple,
                TargetMachine::get_host_cpu_name().to_str().unwrap(),
                TargetMachine::get_host_cpu_features().to_str().unwrap(),
                opt_level,
                RelocMode::PIC,
                CodeModel::Default,
            )
            .ok_or("failed to create target machine".to_owned())?;
        let context = inkwell::context::Context::create();
        let code_gen = CodeGen {
            context: &context,
            module: context.create_module("hpbf"),
            builder: context.create_builder(),
        };
        code_gen.module.set_triple(&triple);
        code_gen
            .module
            .set_data_layout(&target_machine.get_target_data().get_data_layout());
        code_gen.compile_program(program)?;
        if opt != 0 {
            code_gen
                .module
                .run_passes(
                    &format!("default<O{opt}>"),
                    &target_machine,
                    PassBuilderOptions::create(),
                )
                .map_err(|err| err.to_string())?;
        }
        let execution_engine = code_gen
            .module
            .create_jit_execution_engine(opt_level)
            .map_err(|err| err.to_string())?;
        unsafe {
            let func: JitFunction<HpbfEntry<'a, C>> = execution_engine
                .get_function("hpbf_entry")
                .map_err(|err| err.to_string())?;
            func.call(self);
        }
        Ok(())
    }
}
