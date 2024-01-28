use inkwell::{
    attributes::{Attribute, AttributeLoc},
    basic_block::BasicBlock,
    builder::{Builder, BuilderError},
    execution_engine::JitFunction,
    module::Module,
    passes::PassBuilderOptions,
    targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetData, TargetMachine},
    values::{FunctionValue, PointerValue},
    AddressSpace, IntPredicate, OptimizationLevel,
};

use crate::{Block, CellType, Context, Instr};

type HpbfEntry<'a, 'b, C> = unsafe extern "C" fn(cxt: &'b mut Context<'a, C>);

struct CodeGen<'cxt> {
    context: &'cxt inkwell::context::Context,
    module: Module<'cxt>,
    builder: Builder<'cxt>,
    target_data: TargetData,
    target_machine: TargetMachine,
    runtime_extend: FunctionValue<'cxt>,
    runtime_input: FunctionValue<'cxt>,
    runtime_output: FunctionValue<'cxt>,
}

impl<'cxt> CodeGen<'cxt> {
    fn compile_block<C: CellType>(
        &self,
        block: &Block<C>,
        function: FunctionValue<'cxt>,
        mut prev_block: BasicBlock<'cxt>,
        cxt_ptr: PointerValue<'cxt>,
        cond: Option<isize>,
    ) -> Result<(bool, Option<(isize, isize)>), BuilderError> {
        let mut moved = false;
        let mut accessed = None;
        let mut current_start = self.context.append_basic_block(function, "body");
        let mut current_block = current_start;
        self.builder.position_at_end(current_block);
        for instr in block {
            match instr {
                Instr::Move(offset) => {
                    if let Some((start, end)) = &mut accessed {
                        *start = isize::min(*start, *offset);
                        *end = isize::max(*end, *offset + 1);
                    } else {
                        accessed = Some((*offset, *offset + 1));
                    }
                    let new_ptr = self.build_load_pointer::<C>(cxt_ptr, *offset, true)?;
                    self.build_store_pointer::<C>(cxt_ptr, new_ptr)?;
                    self.builder.position_at_end(prev_block);
                    if let Some((start, end)) = accessed {
                        self.build_bounds_checks::<C>(
                            function,
                            current_start,
                            cxt_ptr,
                            start,
                            end,
                        )?;
                        accessed = None;
                    } else {
                        self.builder.build_unconditional_branch(current_start)?;
                    }
                    let next_block = self.context.append_basic_block(function, "body");
                    self.builder.position_at_end(next_block);
                    prev_block = current_block;
                    current_start = next_block;
                    current_block = next_block;
                    moved = true;
                }
                Instr::Load(val, dst) => {
                    if let Some((start, end)) = &mut accessed {
                        *start = isize::min(*start, *dst);
                        *end = isize::max(*end, *dst + 1);
                    } else {
                        accessed = Some((*dst, *dst + 1));
                    }
                    let int_type = self.context.custom_width_int_type(C::BITS);
                    let ptr = self.build_load_pointer::<C>(cxt_ptr, *dst, true)?;
                    self.builder
                        .build_store(ptr, int_type.const_int(val.into_u64(), false))?;
                }
                Instr::Add(val, dst) => {
                    if let Some((start, end)) = &mut accessed {
                        *start = isize::min(*start, *dst);
                        *end = isize::max(*end, *dst + 1);
                    } else {
                        accessed = Some((*dst, *dst + 1));
                    }
                    let int_type = self.context.custom_width_int_type(C::BITS);
                    let ptr = self.build_load_pointer::<C>(cxt_ptr, *dst, true)?;
                    let old_value = self
                        .builder
                        .build_load(int_type, ptr, "add_original")?
                        .into_int_value();
                    let new_value = self.builder.build_int_add(
                        old_value,
                        int_type.const_int(val.into_u64(), false),
                        "add_result",
                    )?;
                    self.builder.build_store(ptr, new_value)?;
                }
                Instr::MulAdd(val, src, dst) => {
                    if let Some((start, end)) = &mut accessed {
                        *start = isize::min(*start, isize::min(*dst, *src));
                        *end = isize::max(*end, isize::max(*dst, *src) + 1);
                    } else {
                        accessed = Some((isize::min(*dst, *src), isize::max(*dst, *src) + 1));
                    }
                    let int_type = self.context.custom_width_int_type(C::BITS);
                    let src_ptr = self.build_load_pointer::<C>(cxt_ptr, *src, true)?;
                    let dst_ptr = self.build_load_pointer::<C>(cxt_ptr, *dst, true)?;
                    let src_value = self
                        .builder
                        .build_load(int_type, src_ptr, "mul_original")?
                        .into_int_value();
                    let dst_value = self
                        .builder
                        .build_load(int_type, dst_ptr, "muladd_original")?
                        .into_int_value();
                    let mul_result_value = self.builder.build_int_mul(
                        src_value,
                        int_type.const_int(val.into_u64(), false),
                        "mul_result",
                    )?;
                    let new_value =
                        self.builder
                            .build_int_add(dst_value, mul_result_value, "muladd_result")?;
                    self.builder.build_store(dst_ptr, new_value)?;
                }
                Instr::Output(src) => {
                    if let Some((start, end)) = &mut accessed {
                        *start = isize::min(*start, *src);
                        *end = isize::max(*end, *src + 1);
                    } else {
                        accessed = Some((*src, *src + 1));
                    }
                    let int_type = self.context.custom_width_int_type(C::BITS);
                    let ptr = self.build_load_pointer::<C>(cxt_ptr, *src, true)?;
                    let src_value = self
                        .builder
                        .build_load(int_type, ptr, "output")?
                        .into_int_value();
                    self.builder.build_call(
                        self.runtime_output,
                        &[cxt_ptr.into(), src_value.into()],
                        "",
                    )?;
                }
                Instr::Input(dst) => {
                    if let Some((start, end)) = &mut accessed {
                        *start = isize::min(*start, *dst);
                        *end = isize::max(*end, *dst + 1);
                    } else {
                        accessed = Some((*dst, *dst + 1));
                    }
                    let new_value = self
                        .builder
                        .build_call(self.runtime_input, &[cxt_ptr.into()], "input")?
                        .try_as_basic_value()
                        .unwrap_left();
                    let ptr = self.build_load_pointer::<C>(cxt_ptr, *dst, true)?;
                    self.builder.build_store(ptr, new_value)?;
                }
                Instr::Loop(cond, block) => {
                    if let Some((start, end)) = &mut accessed {
                        *start = isize::min(*start, *cond);
                        *end = isize::max(*end, *cond + 1);
                    } else {
                        accessed = Some((*cond, *cond + 1));
                    }
                    let cond_block = self.context.append_basic_block(function, "loop_cond");
                    self.builder.build_unconditional_branch(cond_block)?;
                    self.builder.position_at_end(cond_block);
                    let int_type = self.context.custom_width_int_type(C::BITS);
                    let cond_ptr = self.build_load_pointer::<C>(cxt_ptr, *cond, true)?;
                    let cond_value = self
                        .builder
                        .build_load(int_type, cond_ptr, "loop_cond")?
                        .into_int_value();
                    let cmp_value = self.builder.build_int_compare(
                        IntPredicate::NE,
                        cond_value,
                        int_type.const_zero(),
                        "loop_cmp",
                    )?;
                    let loop_block = self.context.append_basic_block(function, "loop_body");
                    let next_block = self.context.append_basic_block(function, "body");
                    self.builder
                        .build_conditional_branch(cmp_value, loop_block, next_block)?;
                    let (sub_moved, sub_accessed) =
                        self.compile_block(block, function, loop_block, cxt_ptr, Some(*cond))?;
                    self.builder.build_unconditional_branch(cond_block)?;
                    current_block = next_block;
                    if sub_moved {
                        self.builder.position_at_end(prev_block);
                        if let Some((start, end)) = accessed {
                            self.build_bounds_checks::<C>(
                                function,
                                current_start,
                                cxt_ptr,
                                start,
                                end,
                            )?;
                            accessed = None;
                        } else {
                            self.builder.build_unconditional_branch(current_start)?;
                        }
                        let next_block = self.context.append_basic_block(function, "body");
                        self.builder.position_at_end(next_block);
                        prev_block = current_block;
                        current_start = next_block;
                        current_block = next_block;
                        moved = true;
                    }
                    if let Some((sub_start, sub_end)) = sub_accessed {
                        if let Some((start, end)) = &mut accessed {
                            *start = isize::min(*start, sub_start);
                            *end = isize::max(*end, sub_end);
                        } else {
                            accessed = sub_accessed;
                        }
                    }
                    self.builder.position_at_end(current_block);
                }
                Instr::If(cond, block) => {
                    if let Some((start, end)) = &mut accessed {
                        *start = isize::min(*start, *cond);
                        *end = isize::max(*end, *cond + 1);
                    } else {
                        accessed = Some((*cond, *cond + 1));
                    }
                    let int_type = self.context.custom_width_int_type(C::BITS);
                    let cond_ptr = self.build_load_pointer::<C>(cxt_ptr, *cond, true)?;
                    let cond_value = self
                        .builder
                        .build_load(int_type, cond_ptr, "if_cond")?
                        .into_int_value();
                    let cmp_value = self.builder.build_int_compare(
                        IntPredicate::NE,
                        cond_value,
                        int_type.const_zero(),
                        "if_cmp",
                    )?;
                    let if_block = self.context.append_basic_block(function, "if_body");
                    let next_block = self.context.append_basic_block(function, "body");
                    self.builder
                        .build_conditional_branch(cmp_value, if_block, next_block)?;
                    let (sub_moved, sub_accessed) =
                        self.compile_block(block, function, if_block, cxt_ptr, None)?;
                    self.builder.build_unconditional_branch(next_block)?;
                    current_block = next_block;
                    if sub_moved {
                        self.builder.position_at_end(prev_block);
                        if let Some((start, end)) = accessed {
                            self.build_bounds_checks::<C>(
                                function,
                                current_start,
                                cxt_ptr,
                                start,
                                end,
                            )?;
                            accessed = None;
                        } else {
                            self.builder.build_unconditional_branch(current_start)?;
                        }
                        let next_block = self.context.append_basic_block(function, "body");
                        self.builder.position_at_end(next_block);
                        prev_block = current_block;
                        current_start = next_block;
                        current_block = next_block;
                        moved = true;
                    }
                    if let Some((sub_start, sub_end)) = sub_accessed {
                        if let Some((start, end)) = &mut accessed {
                            *start = isize::min(*start, sub_start);
                            *end = isize::max(*end, sub_end);
                        } else {
                            accessed = sub_accessed;
                        }
                    }
                    self.builder.position_at_end(current_block);
                }
            }
        }
        if moved {
            if let Some(cond) = cond {
                if let Some((start, end)) = &mut accessed {
                    *start = isize::min(*start, cond);
                    *end = isize::max(*end, cond + 1);
                } else {
                    accessed = Some((cond, cond + 1));
                }
            }
            self.builder.position_at_end(prev_block);
            if let Some((start, end)) = accessed {
                self.build_bounds_checks::<C>(function, current_start, cxt_ptr, start, end)?;
                accessed = None;
            } else {
                self.builder.build_unconditional_branch(current_start)?;
            }
        } else {
            self.builder.position_at_end(prev_block);
            self.builder.build_unconditional_branch(current_start)?;
        }
        self.builder.position_at_end(current_block);
        Ok((moved, accessed))
    }

    fn build_store_pointer<C: CellType>(
        &self,
        cxt_ptr: PointerValue<'cxt>,
        mem_ptr: PointerValue<'cxt>,
    ) -> Result<(), BuilderError> {
        let int_type = self.context.custom_width_int_type(C::BITS);
        let ptr_type = int_type.ptr_type(AddressSpace::default());
        let cxt_struct_type = self
            .context
            .struct_type(&[ptr_type.into(), ptr_type.into(), ptr_type.into()], false);
        let mem_ptr_ptr =
            self.builder
                .build_struct_gep(cxt_struct_type, cxt_ptr, 2, "mem_ptr_ptr")?;
        self.builder.build_store(mem_ptr_ptr, mem_ptr)?;
        Ok(())
    }

    fn build_load_pointer<C: CellType>(
        &self,
        cxt_ptr: PointerValue<'cxt>,
        offset: isize,
        in_bound: bool,
    ) -> Result<PointerValue<'cxt>, BuilderError> {
        let int_type = self.context.custom_width_int_type(C::BITS);
        let ptr_type = int_type.ptr_type(AddressSpace::default());
        let cxt_struct_type = self
            .context
            .struct_type(&[ptr_type.into(), ptr_type.into(), ptr_type.into()], false);
        let mem_ptr_ptr =
            self.builder
                .build_struct_gep(cxt_struct_type, cxt_ptr, 2, "mem_ptr_ptr")?;
        let mem_ptr = self
            .builder
            .build_load(ptr_type, mem_ptr_ptr, "mem_ptr")?
            .into_pointer_value();
        let offset = self
            .context
            .ptr_sized_int_type(&self.target_data, None)
            .const_int(offset as u64, true);
        let mem_ptr_offset = unsafe {
            if in_bound {
                self.builder
                    .build_in_bounds_gep(int_type, mem_ptr, &[offset], "mem_ptr_offset")?
            } else {
                self.builder
                    .build_gep(int_type, mem_ptr, &[offset], "mem_ptr_offset")?
            }
        };
        Ok(mem_ptr_offset)
    }

    fn build_load_pointers<C: CellType>(
        &self,
        cxt_ptr: PointerValue<'cxt>,
    ) -> Result<[PointerValue<'cxt>; 2], BuilderError> {
        let int_type = self.context.custom_width_int_type(C::BITS);
        let ptr_type = int_type.ptr_type(AddressSpace::default());
        let cxt_struct_type = self
            .context
            .struct_type(&[ptr_type.into(), ptr_type.into(), ptr_type.into()], false);
        let mem_ptr_low =
            self.builder
                .build_struct_gep(cxt_struct_type, cxt_ptr, 0, "mem_low_ptr")?;
        let mem_low = self
            .builder
            .build_load(ptr_type, mem_ptr_low, "mem_low")?
            .into_pointer_value();
        let mem_ptr_high =
            self.builder
                .build_struct_gep(cxt_struct_type, cxt_ptr, 1, "mem_high_ptr")?;
        let mem_high = self
            .builder
            .build_load(ptr_type, mem_ptr_high, "mem_high")?
            .into_pointer_value();
        Ok([mem_low, mem_high])
    }

    fn build_bounds_checks<C: CellType>(
        &self,
        function: FunctionValue<'cxt>,
        next_block: BasicBlock<'cxt>,
        cxt_ptr: PointerValue<'cxt>,
        start: isize,
        end: isize,
    ) -> Result<(), BuilderError> {
        let intptr_type = self.context.ptr_sized_int_type(&self.target_data, None);
        let [mem_low, mem_high] = self.build_load_pointers::<C>(cxt_ptr)?;
        let ptr_start = self.build_load_pointer::<C>(cxt_ptr, start, false)?;
        let diff_low = self.builder.build_int_sub(
            self.builder
                .build_ptr_to_int(ptr_start, intptr_type, "ptr_start")?,
            self.builder
                .build_ptr_to_int(mem_low, intptr_type, "mem_low")?,
            "diff_low",
        )?;
        let fail_block = self.context.append_basic_block(function, "check_fail");
        let second_block = self.context.append_basic_block(function, "check_second");
        let cmp_start = self.builder.build_int_compare(
            IntPredicate::SGE,
            diff_low,
            intptr_type.const_zero(),
            "start_cmp",
        )?;
        self.builder
            .build_conditional_branch(cmp_start, second_block, fail_block)?;
        self.builder.position_at_end(second_block);
        let ptr_end = self.build_load_pointer::<C>(cxt_ptr, end, false)?;
        let diff_high = self.builder.build_int_sub(
            self.builder
                .build_ptr_to_int(mem_high, intptr_type, "mem_high")?,
            self.builder
                .build_ptr_to_int(ptr_end, intptr_type, "ptr_end")?,
            "diff_high",
        )?;
        let cmp_end = self.builder.build_int_compare(
            IntPredicate::SGE,
            diff_high,
            intptr_type.const_zero(),
            "end_cmp",
        )?;
        self.builder
            .build_conditional_branch(cmp_end, next_block, fail_block)?;
        self.builder.position_at_end(fail_block);
        self.builder.build_call(
            self.runtime_extend,
            &[
                cxt_ptr.into(),
                intptr_type.const_int(start as u64, true).into(),
                intptr_type.const_int(end as u64, true).into(),
            ],
            "",
        )?;
        self.builder.build_unconditional_branch(next_block)?;
        Ok(())
    }

    fn compile_program<'a, C: CellType>(&self, program: &Block<C>) -> Result<(), BuilderError> {
        let int_type = self.context.custom_width_int_type(C::BITS);
        let void_type = self.context.void_type();
        let ptr_type = int_type.ptr_type(AddressSpace::default());
        let cxt_struct_type = self
            .context
            .struct_type(&[ptr_type.into(), ptr_type.into(), ptr_type.into()], false);
        let function = self.module.add_function(
            "hpbf_program_entry",
            void_type.fn_type(&[ptr_type.into()], false),
            None,
        );
        let noalias_kind = Attribute::get_named_enum_kind_id("noalias");
        function.add_attribute(
            AttributeLoc::Param(0),
            self.context.create_enum_attribute(noalias_kind, 0),
        );
        let nocapture_kind = Attribute::get_named_enum_kind_id("nocapture");
        function.add_attribute(
            AttributeLoc::Param(0),
            self.context.create_enum_attribute(nocapture_kind, 0),
        );
        let noundef_kind = Attribute::get_named_enum_kind_id("noundef");
        function.add_attribute(
            AttributeLoc::Param(0),
            self.context.create_enum_attribute(noundef_kind, 0),
        );
        let align_kind = Attribute::get_named_enum_kind_id("align");
        function.add_attribute(
            AttributeLoc::Param(0),
            self.context.create_enum_attribute(
                align_kind,
                self.target_data.get_abi_alignment(&cxt_struct_type) as u64,
            ),
        );
        let deref_kind = Attribute::get_named_enum_kind_id("dereferenceable");
        function.add_attribute(
            AttributeLoc::Param(0),
            self.context
                .create_enum_attribute(deref_kind, self.target_data.get_abi_size(&cxt_struct_type)),
        );
        let entry_block = self.context.append_basic_block(function, "entry");
        let body_block = self.context.append_basic_block(function, "body");
        let exit_block = self.context.append_basic_block(function, "exit");
        self.builder.position_at_end(entry_block);
        let cxt_ptr = function.get_nth_param(0).unwrap().into_pointer_value();
        let (_, accessed) = self.compile_block(program, function, body_block, cxt_ptr, None)?;
        self.builder.build_unconditional_branch(exit_block)?;
        self.builder.position_at_end(entry_block);
        if let Some((start, end)) = accessed {
            self.build_bounds_checks::<C>(function, body_block, cxt_ptr, start, end)?;
        } else {
            self.builder.build_unconditional_branch(body_block)?;
        }
        self.builder.position_at_end(exit_block);
        self.builder.build_return(None)?;
        Ok(())
    }

    fn create<C: CellType>(
        context: &'cxt inkwell::context::Context,
        opt: u32,
        program: &Block<C>,
    ) -> Result<Self, String> {
        let opt_level = match opt {
            0 => OptimizationLevel::None,
            1 => OptimizationLevel::Less,
            2 => OptimizationLevel::Default,
            _ => OptimizationLevel::Aggressive,
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
        let target_data = target_machine.get_target_data();
        let module = context.create_module("hpbf");
        let builder = context.create_builder();
        module.set_triple(&triple);
        module.set_data_layout(&target_data.get_data_layout());
        let int_type = context.custom_width_int_type(C::BITS);
        let intptr_type = context.ptr_sized_int_type(&target_data, None);
        let void_type = context.void_type();
        let ptr_type = int_type.ptr_type(AddressSpace::default());
        let readnone_kind = Attribute::get_named_enum_kind_id("readnone");
        let nocapture_kind = Attribute::get_named_enum_kind_id("nocapture");
        let cold_kind = Attribute::get_named_enum_kind_id("cold");
        let memory_kind = Attribute::get_named_enum_kind_id("memory");
        let noalias_kind = Attribute::get_named_enum_kind_id("noalias");
        let runtime_extend = module.add_function(
            "hpbf_context_extend",
            void_type.fn_type(
                &[ptr_type.into(), intptr_type.into(), intptr_type.into()],
                false,
            ),
            None,
        );
        runtime_extend.add_attribute(
            AttributeLoc::Param(0),
            context.create_enum_attribute(nocapture_kind, 0),
        );
        runtime_extend.add_attribute(
            AttributeLoc::Param(0),
            context.create_enum_attribute(noalias_kind, 0),
        );
        runtime_extend.add_attribute(
            AttributeLoc::Function,
            context.create_enum_attribute(cold_kind, 0),
        );
        runtime_extend.add_attribute(
            AttributeLoc::Function,
            context.create_enum_attribute(memory_kind, 0xf),
        );
        let runtime_input = module.add_function(
            "hpbf_context_input",
            int_type.fn_type(&[ptr_type.into()], false),
            None,
        );
        runtime_input.add_attribute(
            AttributeLoc::Param(0),
            context.create_enum_attribute(readnone_kind, 0),
        );
        runtime_input.add_attribute(
            AttributeLoc::Param(0),
            context.create_enum_attribute(nocapture_kind, 0),
        );
        runtime_input.add_attribute(
            AttributeLoc::Function,
            context.create_enum_attribute(memory_kind, 0xc),
        );
        let runtime_output = module.add_function(
            "hpbf_context_output",
            void_type.fn_type(&[ptr_type.into(), int_type.into()], false),
            None,
        );
        runtime_output.add_attribute(
            AttributeLoc::Param(0),
            context.create_enum_attribute(readnone_kind, 0),
        );
        runtime_output.add_attribute(
            AttributeLoc::Param(0),
            context.create_enum_attribute(nocapture_kind, 0),
        );
        runtime_output.add_attribute(
            AttributeLoc::Function,
            context.create_enum_attribute(memory_kind, 0xc),
        );
        let code_gen = CodeGen {
            context,
            module,
            builder,
            target_data,
            target_machine,
            runtime_extend,
            runtime_input,
            runtime_output,
        };
        code_gen
            .compile_program(program)
            .map_err(|err| err.to_string())?;
        code_gen.module.verify().map_err(|err| err.to_string())?;
        if opt != 0 {
            code_gen
                .module
                .run_passes(
                    &format!("default<O{opt}>"),
                    &code_gen.target_machine,
                    PassBuilderOptions::create(),
                )
                .map_err(|err| err.to_string())?;
            code_gen.module.verify().map_err(|err| err.to_string())?;
        }
        Ok(code_gen)
    }
}

impl<'a, C: CellType> Context<'a, C> {
    pub fn jit_print_module<'b>(&'b mut self, opt: u32, program: &Block<C>) -> Result<(), String> {
        let context = inkwell::context::Context::create();
        let code_gen = CodeGen::create(&context, opt, program)?;
        code_gen.module.print_to_stderr();
        Ok(())
    }

    pub fn jit_execute<'b>(&'b mut self, opt: u32, program: &Block<C>) -> Result<(), String> {
        let opt_level = match opt {
            0 => OptimizationLevel::None,
            1 => OptimizationLevel::Less,
            2 => OptimizationLevel::Default,
            _ => OptimizationLevel::Aggressive,
        };
        let context = inkwell::context::Context::create();
        let code_gen = CodeGen::create(&context, opt, program)?;
        let execution_engine = code_gen
            .module
            .create_jit_execution_engine(opt_level)
            .map_err(|err| err.to_string())?;
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
            let func: JitFunction<HpbfEntry<'a, 'b, C>> = execution_engine
                .get_function("hpbf_program_entry")
                .map_err(|err| err.to_string())?;
            func.call(self);
        }
        Ok(())
    }
}

extern "C" fn hpbf_context_extend<C: CellType>(
    cxt: &mut Context<'static, C>,
    min: isize,
    max: isize,
) {
    cxt.make_accessible(min, max);
}

extern "C" fn hpbf_context_input<C: CellType>(cxt: &mut Context<'static, C>) -> C {
    C::from_u8(cxt.input())
}

extern "C" fn hpbf_context_output<C: CellType>(cxt: &mut Context<'static, u8>, value: C) {
    cxt.output(value.into_u8());
}

#[cfg(test)]
mod tests {
    use crate::{optimize, parse, Context};

    #[test]
    #[cfg_attr(miri, ignore)]
    fn jit_h() -> Result<(), String> {
        let prog = parse::<u8>("++++++[>+++++<-]>++[>++<-]++++[>++<-]>[.>]")
            .map_err(|_| "parsing failed".to_owned())?;
        let prog = optimize(prog);
        let mut buf = Vec::new();
        let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
        ctx.jit_execute(3, &prog)?;
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "H");
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn jit_hello_world_no_opt() -> Result<(), String> {
        let prog = parse::<u8>(
            "++++++[>+++++<-]>++[>++>+++>+++>+++>+++>+>+++>+++>++++>+++>++
            +>+[<]>-]++++[>++>+>+++>+++>+++>>-->+++>--->+++>+>>++
            [<]>-]>>+>>>+++>>->+++>-->>>+>++[<]>[.>]",
        )
        .map_err(|_| "parsing failed".to_owned())?;
        let mut buf = Vec::new();
        let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
        ctx.jit_execute(0, &prog)?;
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn jit_hello_world() -> Result<(), String> {
        let prog = parse::<u8>(
            "++++++[>+++++<-]>++[>++>+++>+++>+++>+++>+>+++>+++>++++>+++>++
            +>+<<<<<<<<<<<<-]++++[>++>+>+++>+++>+++>>-->+++>--->+++>+>>++
            <<<<<<<<<<<<<-]>>+>>>+++>>->+++>-->>>+>++<<<<<<<<<<<<<>[.>]",
        )
        .map_err(|_| "parsing failed".to_owned())?;
        let prog = optimize(prog);
        let mut buf = Vec::new();
        let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
        ctx.jit_execute(3, &prog)?;
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn jit_hello_world_u8() -> Result<(), String> {
        let prog = parse::<u8>(
            ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.",
        )
        .map_err(|_| "parsing failed".to_owned())?;
        let prog = optimize(prog);
        let mut buf = Vec::new();
        let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
        ctx.jit_execute(3, &prog)?;
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn jit_hello_world_u16() -> Result<(), String> {
        let prog = parse::<u16>(
            ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.",
        )
        .map_err(|_| "parsing failed".to_owned())?;
        let prog = optimize(prog);
        let mut buf = Vec::new();
        let mut ctx = Context::<u16>::new(None, Some(Box::new(&mut buf)));
        ctx.jit_execute(3, &prog)?;
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn jit_hello_world_u32() -> Result<(), String> {
        let prog = parse::<u32>(
            ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.",
        )
        .map_err(|_| "parsing failed".to_owned())?;
        let prog = optimize(prog);
        let mut buf = Vec::new();
        let mut ctx = Context::<u32>::new(None, Some(Box::new(&mut buf)));
        ctx.jit_execute(3, &prog)?;
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn jit_hello_world_u64() -> Result<(), String> {
        let prog = parse::<u64>(
            ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.",
        )
        .map_err(|_| "parsing failed".to_owned())?;
        let prog = optimize(prog);
        let mut buf = Vec::new();
        let mut ctx = Context::<u64>::new(None, Some(Box::new(&mut buf)));
        ctx.jit_execute(3, &prog)?;
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn jit_hello_world_minimal_no_opt() -> Result<(), String> {
        let prog =
            parse::<u8>("+[-->-[>>+>-----<<]<--<---]>-.>>>+.>>..+++[.>]<<<<.+++.------.<<-.>>>>+.")
                .map_err(|_| "parsing failed".to_owned())?;
        let mut buf = Vec::new();
        let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
        ctx.jit_execute(0, &prog)?;
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello, World!");
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn jit_hello_world_minimal() -> Result<(), String> {
        let prog =
            parse::<u8>("+[-->-[>>+>-----<<]<--<---]>-.>>>+.>>..+++[.>]<<<<.+++.------.<<-.>>>>+.")
                .map_err(|_| "parsing failed".to_owned())?;
        let prog = optimize(prog);
        let mut buf = Vec::new();
        let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
        ctx.jit_execute(3, &prog)?;
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello, World!");
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn jit_program_access_distant_cell_no_opt() -> Result<(), String> {
        let mut buf = Vec::new();
        let mut ctx = Context::<u64>::new(None, Some(Box::new(&mut buf)));
        let prog = parse(
            "++++[>++++++<-]>[>+++++>+++++++<<-]>>++++<[[>[[
            >>+<<-]<]>>>-]>-[>+>+<<-]>]+++++[>+++++++<<++>-]>.<<.",
        )
        .map_err(|_| "parsing failed".to_owned())?;
        ctx.jit_execute(0, &prog)?;
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "#\n");
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn jit_program_access_distant_cell() -> Result<(), String> {
        let mut buf = Vec::new();
        let mut ctx = Context::<u64>::new(None, Some(Box::new(&mut buf)));
        let prog = parse(
            "++++[>++++++<-]>[>+++++>+++++++<<-]>>++++<[[>[[
            >>+<<-]<]>>>-]>-[>+>+<<-]>]+++++[>+++++++<<++>-]>.<<.",
        )
        .map_err(|_| "parsing failed".to_owned())?;
        let prog = optimize(prog);
        ctx.jit_execute(3, &prog)?;
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "#\n");
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn jit_program_output_h_no_opt() -> Result<(), String> {
        let mut buf = Vec::new();
        let mut ctx = Context::<u64>::new(None, Some(Box::new(&mut buf)));
        let prog = parse(
            "[]++++++++++[>>+>+>++++++[<<+<+++>>>-]<<<<-]
            \"A*$\";?@![#>>+<<]>[>>]<<<<[>++<[-]]>.>.",
        )
        .map_err(|_| "parsing failed".to_owned())?;
        ctx.jit_execute(3, &prog)?;
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "H\n");
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn jit_program_output_h() -> Result<(), String> {
        let mut buf = Vec::new();
        let mut ctx = Context::<u64>::new(None, Some(Box::new(&mut buf)));
        let prog = parse(
            "[]++++++++++[>>+>+>++++++[<<+<+++>>>-]<<<<-]
            \"A*$\";?@![#>>+<<]>[>>]<<<<[>++<[-]]>.>.",
        )
        .map_err(|_| "parsing failed".to_owned())?;
        let prog = optimize(prog);
        ctx.jit_execute(3, &prog)?;
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "H\n");
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn jit_program_rot13_no_opt() -> Result<(), String> {
        let mut buf = Vec::new();
        let mut ctx = Context::<u8>::new(
            Some(Box::new("~mlk zyx".as_bytes())),
            Some(Box::new(&mut buf)),
        );
        let prog = parse(
            ",
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>++++++++++++++<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>>+++++[<----->-]<<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>++++++++++++++<-
            [>+<-[>+<-[>+<-[>+<-[>+<-
            [>++++++++++++++<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>>+++++[<----->-]<<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>++++++++++++++<-
            [>+<-]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
            ]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]>.[-]<,]",
        )
        .map_err(|_| "parsing failed".to_owned())?;
        ctx.jit_execute(0, &prog)?;
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "~zyx mlk");
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn jit_program_rot13() -> Result<(), String> {
        let mut buf = Vec::new();
        let mut ctx = Context::<u8>::new(
            Some(Box::new("~mlk zyx".as_bytes())),
            Some(Box::new(&mut buf)),
        );
        let prog = parse(
            ",
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>++++++++++++++<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>>+++++[<----->-]<<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>++++++++++++++<-
            [>+<-[>+<-[>+<-[>+<-[>+<-
            [>++++++++++++++<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>>+++++[<----->-]<<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>++++++++++++++<-
            [>+<-]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
            ]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]>.[-]<,]",
        )
        .map_err(|_| "parsing failed".to_owned())?;
        let prog = optimize(prog);
        ctx.jit_execute(3, &prog)?;
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "~zyx mlk");
        Ok(())
    }
}
