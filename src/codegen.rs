use std::collections::HashMap;
use std::path::Path;

use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::AddressSpace;
use inkwell::targets::{InitializationConfig, Target, TargetMachine};
use inkwell::passes::PassManager;

use inkwell::types::{
    BasicTypeEnum,
    BasicType,
    BasicMetadataTypeEnum,
    AnyTypeEnum
};

use inkwell::values::{BasicMetadataValueEnum, BasicValue, FunctionValue};

use crate::ast::{
    Program,
    Type,
    Field,
    Function,
    Expression
};

pub struct Compiler<'a, 'ctx> {
    pub context: &'ctx Context,
    pub builder: &'a Builder<'ctx>,
    pub module: &'a Module<'ctx>,
    pub fpm: &'a PassManager<FunctionValue<'ctx>>,
    
    pub types: HashMap<String, BasicTypeEnum<'ctx>>,
    pub variables: HashMap<String, BasicMetadataValueEnum<'ctx>>,
}

impl Program {
    pub fn compile(&self) {
        let context = Context::create();
        let module = context.create_module("main");
        let builder = context.create_builder();

        let fpm = PassManager::create(&module);
        fpm.add_instruction_combining_pass();
        fpm.add_reassociate_pass();
        fpm.add_gvn_pass();
        fpm.add_cfg_simplification_pass();
        fpm.add_basic_alias_analysis_pass();
        fpm.add_promote_memory_to_register_pass();
        fpm.add_instruction_combining_pass();
        fpm.add_reassociate_pass();

        let mut compiler = Compiler {
            context: &context,
            module: &module,
            builder: &builder,
            fpm: &fpm,

            types: HashMap::new(),
            variables: HashMap::new(),
        };

        // Insert types for builtin functions
        let memget_t = Type::Func(
                "memget".to_string(), 
                Box::new(Field::I64),
                Box::new(Field::I64)
        );
        memget_t.compile(Some(&"memget".to_string()), &mut compiler);

        let memset_t = Type::Func(
                "memget".to_string(), 
                Box::new(Field::Tuple(vec![Field::I64, Field::I64])),
                Box::new(Field::Empty)
        );
        memset_t.compile(Some(&"memget".to_string()), &mut compiler);

        for (name, ty) in self.types.iter() {
            ty.compile(Some(name), &mut compiler);
        }

        for (name, func) in self.funcs.iter() {
            let f = compiler.module.get_function(name).unwrap();

            let entry = compiler.context.append_basic_block(f, "entry");
            compiler.builder.position_at_end(entry);

            if func.len() == 1 {
                // Add function args...
                let params = f.get_params();
                for (i, a) in func[0].args.iter().enumerate() {
                    let name = match a {
                        Expression::Identifier(_, n) => n.clone(),
                        _ => format!("{i}")
                    };

                    compiler.variables.insert(name, params[i].into());
                }

                func[0].codegen(&mut compiler);
                compiler.builder.build_return(None);
            } else {
                panic!("WHOAH THERE!!!") //TODO
            }
        }

        compiler.module.print_to_stderr();
        compiler.module.verify().unwrap();
        compiler.module.write_bitcode_to_path(Path::new("module.bc"));

        // Compile to object file!
        let init_config = InitializationConfig {
            info: true,
            base: true,
            machine_code: true,
            asm_parser: true,
            asm_printer: true,
            disassembler: false,
        };

        Target::initialize_native(&init_config).unwrap();

        let triple = TargetMachine::get_default_triple();
        let target = Target::from_triple(&triple).unwrap();

        let tm = target.create_target_machine(
            &triple,
            "generic",
            "",
            inkwell::OptimizationLevel::Default,
            inkwell::targets::RelocMode::PIC,
            inkwell::targets::CodeModel::Default
        ).unwrap();

        compiler.module.set_data_layout(&tm.get_target_data().get_data_layout());

        // Emit object code!!!
        tm.write_to_file(
            compiler.module,
            inkwell::targets::FileType::Object,
            Path::new("output.o")
        ).unwrap();
    }
}

impl Type {
    fn compile<'a, 'ctx>(&self, name: Option<&String>, c: &mut Compiler<'a, 'ctx>) -> AnyTypeEnum<'ctx> {
        match self {
            Type::Func(_, a, b) => {
                // Get function type
                let ft = if **b == Field::Empty {
                    let out = c.context.void_type();

                    if let Field::Tuple(fs) = &**a {
                        let args = fs.into_iter()
                            .map(|f| f.compile(c).into())
                            .collect::<Vec<BasicMetadataTypeEnum>>();
                        out.fn_type(args.as_slice(), false)
                    } else {
                        out.fn_type(&[], false)
                    }
                } else {
                    let out = Box::new(b.compile(c)) as Box<dyn BasicType>;

                    if let Field::Tuple(fs) = &**a {
                        let args = fs.into_iter()
                            .map(|f| f.compile(c).into())
                            .collect::<Vec<BasicMetadataTypeEnum>>();
                        out.fn_type(args.as_slice(), false)
                    } else {
                        let arg = a.compile(c).into();
                        out.fn_type(&[arg], false)
                    }
                };

                if let Some(s) = name {
                    c.module.add_function(s.as_str(), ft, None);
                }

                ft.into()
            }
            _ => unimplemented!()
        }
    }
}


impl Field {
    fn compile<'ctx>(&self, c: &mut Compiler<'_, 'ctx>) -> BasicTypeEnum<'ctx> {
        match self {
            Field::U8 | Field::I8 => {
                c.context.i8_type().into()
            },
            Field::U16 | Field::I16 => {
                c.context.i16_type().into()
            },
            Field::U32 | Field::I32 => {
                c.context.i32_type().into()
            },
            Field::U64 | Field::I64 => {
                c.context.i64_type().into()
            },
            Field::Ident(n) => {
                *c.types.get(n).unwrap()
            },
            Field::Str => {
                let char_type = c.context.i8_type();
                char_type.ptr_type(AddressSpace::default()).into()
            }
            Field::Func(_, _) => {
                c.context.i32_type().into()
            }
            Field::Named(_, f) => {
                f.compile(c)
            }
            _ => unimplemented!()
        }
    }
}

pub trait CodeGen {
    fn codegen<'ctx>(&self, c: &mut Compiler<'_, 'ctx>) -> BasicMetadataValueEnum<'ctx>; 
}

impl CodeGen for Function {
    fn codegen<'ctx>(&self, c: &mut Compiler<'_, 'ctx>) -> BasicMetadataValueEnum<'ctx> {
        for i in 0..self.body.len()-1 {
            self.body[i].codegen(c);
        }

        self.body[self.body.len()-1].codegen(c)
    }
}

impl CodeGen for Expression {
    fn codegen<'ctx>(&self, c: &mut Compiler<'_, 'ctx>) -> BasicMetadataValueEnum<'ctx> {
        match self {
            Expression::Num(_, n) => c.context.i64_type().const_int(*n, false).into(),
            Expression::Add(_, left, right) => {
                let (l, r) = (left.codegen(c).into_int_value(), right.codegen(c).into_int_value());
                c.builder.build_int_add(l, r, "addtmp").into()
            }
            Expression::Sub(_, left, right) => {
                let (l, r) = (
                    left.codegen(c).into_int_value(),
                    right.codegen(c).into_int_value()
                );
                c.builder.build_int_sub(l, r, "subtmp").into()
            }
            Expression::Mul(_, left, right) => {
                let (l, r) = (left.codegen(c).into_int_value(), right.codegen(c).into_int_value());
                c.builder.build_int_mul(l, r, "multmp").into()
            }
            Expression::Let(_, name, expr) => {
                let e = expr.codegen(c);
                c.variables.insert(name.clone(), e);
                e.into()
            }
            Expression::Identifier(_, name) => {
                *c.variables.get(name).unwrap()
            }
            Expression::Call(_, name, args) => {
                let args = args.iter()
                    .map(|a| a.codegen(c))
                    .collect::<Vec<BasicMetadataValueEnum>>();

                if let Expression::Identifier(_, i) = &**name {
                    match i.as_str() {
                        i => {
                            let f = c.module.get_function(i).unwrap();

                            c.builder
                                .build_call(f, args.as_slice(), "tmp")
                                .try_as_basic_value().left().unwrap()
                                .into()
                        }
                    }

                } else {
                    panic!("OH NOSES")
                }
            }
            Expression::String(_, s) => {
                c.builder.build_global_string_ptr(&s, &s).as_basic_value_enum().into()
            }
            e => panic!("NOT IMPLEMENTED YET: {e:?}")
        }
    }
}
