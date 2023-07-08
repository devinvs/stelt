use crate::lir::{LIRExpression, LIRTree};
use std::collections::HashMap;

use crate::builtin::BUILTIN_ASM;
use std::error::Error;
use std::io::Write;

use crate::llvm::LLVMType;

pub struct Module {
    w: Box<dyn Write>,
    strs: Vec<String>,

    named_vars: HashMap<String, String>,

    // index for anonymous variables
    i: usize,
    labi: usize,
}

impl Write for Module {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.w.write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.w.flush()
    }
}

impl Module {
    pub fn new(w: Box<dyn Write>) -> Self {
        let mut named_vars = HashMap::new();
        named_vars.insert("arg.0".to_string(), "%arg.0".to_string());

        Self {
            w,
            strs: Vec::new(),
            named_vars,

            i: 1,
            labi: 1,
        }
    }

    pub fn var(&mut self) -> String {
        self.i += 1;
        format!("%anon.{}", self.i - 1)
    }

    pub fn label(&mut self) -> String {
        self.labi += 1;
        format!("Label{}", self.labi - 1)
    }

    pub fn reset(&mut self) {
        self.named_vars.clear();
        self.named_vars
            .insert("arg.0".to_string(), "%arg.0".to_string());
    }

    pub fn compile(&mut self, tree: LIRTree) -> Result<(), Box<dyn Error>> {
        // output builtin functions
        writeln!(self, "{}", &BUILTIN_ASM)?;

        // Output extern functions
        for name in tree.external {
            let (from, to) = tree.extern_types.get(&name).unwrap();

            write!(self, "declare {to} @{name}(")?;

            for (i, f) in from.iter().enumerate() {
                let attrs = if *f == LLVMType::Ptr {
                    " nocapture"
                } else {
                    ""
                };
                if i == 0 {
                    write!(self, "{f}{attrs}")?;
                } else {
                    write!(self, ", {f}{attrs}")?;
                }
            }

            writeln!(self, ") nounwind")?;
        }

        writeln!(self)?;

        // Output all named structs
        for (name, t) in tree.structs.iter() {
            writeln!(self, "%{} = type {}\n", name, t)?;
        }

        // Output all enum types
        for (name, t) in tree.enums.iter() {
            writeln!(self, "%{} = type {}", name, t)?;

            // ... and their variants
            for (vname, t) in tree.variants[name].iter() {
                writeln!(self, "%{}.{} = type {}", name, vname, t)?;
            }

            writeln!(self)?;
        }

        writeln!(self)?;

        // Output struct constructors
        for (name, t) in tree.structs {
            writeln!(self, "define %{name} @{name} ({t} %in) {{")?;

            let out = match t.clone() {
                LLVMType::Struct(ts) => {
                    let mut v = self.var();
                    let w = self.var();
                    let ty = &ts[0];

                    writeln!(self, "\t{w} = extractvalue {t} %in, 0")?;
                    writeln!(self, "\t{v} = insertvalue %{name} undef, {ty} {w}, 0")?;

                    for (i, ty) in ts[1..].iter().enumerate() {
                        let old = v;
                        let w = self.var();
                        v = self.var();

                        writeln!(self, "\t{w} = extractvalue {t} %in, {}", i + 1)?;
                        writeln!(
                            self,
                            "\t{v} = insertvalue %{name} {old}, {ty} {w}, {}",
                            i + 1
                        )?;
                    }

                    v
                }
                _ => panic!("this probably shouldn't happen"),
            };

            writeln!(self, "\tret %{name} {out}")?;
            writeln!(self, "}}\n")?;
        }

        // Output enum constructors
        for (name, _) in tree.enums {
            for (i, (varname, t)) in tree.variants[&name].iter().enumerate() {
                let (t, structargs) = match t.clone() {
                    LLVMType::Struct(mut ts) => {
                        ts.remove(0);

                        if ts.len() == 0 {
                            (LLVMType::Void, true)
                        } else if ts.len() == 1 {
                            (ts[0].clone(), false)
                        } else {
                            (LLVMType::Struct(ts), true)
                        }
                    }
                    _ => unreachable!(),
                };

                if t == LLVMType::Void {
                    writeln!(self, "define %{name} @{varname} () {{")?;
                } else {
                    writeln!(self, "define %{name} @{varname} ({t} %in) {{")?;
                }

                writeln!(self, "\t%ptr = alloca %{name}")?;

                // store enum tag
                writeln!(self, "\tstore i8 {i}, ptr %ptr")?;

                if structargs {
                    // store rest of fields
                    let ts = match t.clone() {
                        LLVMType::Struct(ts) => ts,
                        LLVMType::Void => vec![],
                        _ => unreachable!(),
                    }
                    .into_iter();

                    for (i, t2) in ts.enumerate() {
                        let v = self.var();
                        let i_ptr = self.var();

                        writeln!(self, "\t{v} = extractvalue {t} %in, {i}")?;
                        writeln!(self, "\t{i_ptr} = getelementptr inbounds %{name}.{varname}, ptr %ptr, i32 0, i32 {}", i+1)?;
                        writeln!(self, "\tstore {t2} {v}, ptr {i_ptr}")?;
                    }
                } else {
                    // get pointer to and store single value
                    writeln!(
                        self,
                        "\t%var = getelementptr inbounds %{name}.{varname}, ptr %ptr, i32 0, i32 1"
                    )?;
                    writeln!(self, "\tstore {t} %in, ptr %var")?;
                }

                writeln!(self, "\n\t%ret = load %{name}, ptr %ptr")?;
                writeln!(self, "\tret %{name} %ret")?;
                writeln!(self, "}}\n")?;
            }
        }

        // Compile all functions
        self.reset();
        for (name, expr) in tree.funcs {
            // get function type
            let (from, to) = tree.func_types.get(&name).unwrap();

            if *from == LLVMType::Void {
                writeln!(self, "define {to} @{name}() {{")?;
            } else {
                writeln!(self, "define {to} @{name}({from} %arg.0) {{")?;
            }

            let var = expr.compile(self)?;

            if *to == LLVMType::Void {
                writeln!(self, "\tret {to}")?;
            } else {
                writeln!(self, "\tret {to} {}", var.unwrap())?;
            }

            writeln!(self, "}}\n")?;
            self.reset();
        }

        // Emit string definitions
        for (i, s) in self.strs.clone().into_iter().enumerate() {
            let len = s.len() + 1; // plus one because null byte
            let s = s.replace("\n", "\\0a");

            writeln!(
                self,
                "@str.{i} = private unnamed_addr constant [{len} x i8] c\"{s}\\00\""
            )?;
        }

        Ok(())
    }
}

impl LIRExpression {
    fn compile(self, module: &mut Module) -> Result<Option<String>, Box<dyn Error>> {
        match self {
            Self::If(cond, yes, no, t) => {
                let out = module.var();

                if t != LLVMType::Void {
                    writeln!(module, "\t{out} = alloca {t}")?;
                }

                let cond = cond.compile(module)?.unwrap();

                let yeslab = module.label();
                let nolab = module.label();
                let endlab = module.label();

                writeln!(module, "\tbr i1 {cond}, label %{yeslab}, label %{nolab}")?;

                writeln!(module, "{}:", yeslab)?;
                let yes = yes.compile(module)?;
                if t != LLVMType::Void {
                    writeln!(module, "\tstore {t} {}, ptr {out}", yes.unwrap())?;
                }
                writeln!(module, "\tbr label %{endlab}")?;

                writeln!(module, "{}:", nolab)?;
                let no = no.compile(module)?;
                if t != LLVMType::Void {
                    writeln!(module, "\tstore {t} {}, ptr {out}", no.unwrap())?;
                }
                writeln!(module, "\tbr label %{endlab}")?;

                writeln!(module, "{}:", endlab)?;
                let fin = module.var();
                if t != LLVMType::Void {
                    writeln!(module, "\t{fin} = load {t}, ptr {out}")?;
                    Ok(Some(fin))
                } else {
                    Ok(None)
                }
            }
            Self::Identifier(n, _) => {
                if let Some(var) = module.named_vars.get(&n) {
                    Ok(Some(var.clone()))
                } else {
                    Ok(Some(format!("@{n}")))
                }
            }
            Self::ExternCall(f, args, t) => {
                let out = module.var();

                let mut a = vec![];
                let mut ts = vec![];
                for arg in args {
                    ts.push(arg.ty());
                    a.push(arg.compile(module)?);
                }

                write!(module, "\t")?;

                if t != LLVMType::Void {
                    write!(module, "{out} = ")?;
                }

                write!(module, "call {t} @{f}(")?;

                for i in 0..a.len() {
                    let arg = a[i].as_ref().unwrap();
                    let ty = &ts[i];

                    if i == 0 {
                        write!(module, "{ty} {arg}")?;
                    } else {
                        write!(module, ", {ty} {arg}")?;
                    }
                }

                writeln!(module, ")")?;

                if t != LLVMType::Void {
                    Ok(None)
                } else {
                    Ok(Some(out))
                }
            }
            Self::GlobalCall(f, args, t) => {
                let argt = args.ty();
                let args = args.compile(module)?;
                let out = module.var();

                let args = if let Some(args) = args {
                    format!("({argt} {args})")
                } else {
                    format!("()")
                };

                if t == LLVMType::Void {
                    writeln!(module, "\tcall {t} @{f}{args}")?; // FIX!!!
                    Ok(None)
                } else {
                    // get type of function
                    writeln!(module, "\t{out} = call {t} @{f}{args}")?; // FIX!!!

                    Ok(Some(out))
                }
            }
            Self::Call(f, args, t) => {
                let clos_t = f.ty();

                let arg_count = match args.ty() {
                    LLVMType::Struct(ts) => ts.len(),
                    LLVMType::Void => 0,
                    _ => 1,
                };

                let arg_t = match clos_t.clone() {
                    LLVMType::Struct(ts) => match &ts[0] {
                        LLVMType::Func(args, _) => args.clone(),
                        _ => panic!(),
                    },
                    _ => panic!(),
                };

                let closure = f.compile(module)?.unwrap();

                let mut args = match arg_count {
                    0 => "undef".to_string(),
                    1 => {
                        // create a tuple
                        let tup = LIRExpression::Tuple(vec![*args], *arg_t.clone());
                        tup.compile(module)?.unwrap()
                    }
                    _ => args.compile(module)?.unwrap(),
                };

                let formals = match clos_t.clone() {
                    LLVMType::Struct(mut ts) => {
                        ts.remove(0);
                        ts
                    }
                    _ => panic!(),
                };

                // Get function pointer
                let f = module.var();
                writeln!(module, "\t{f} = extractvalue {clos_t} {closure}, 0")?;

                // insert formals into args struct
                for i in 0..formals.len() {
                    let ft = &formals[i];

                    // get the formal from the closure tuple
                    let v = module.var();
                    writeln!(module, "\t{v} = extractvalue {clos_t} {closure}, {}", i + 1)?;

                    // insert into the args
                    let w = module.var();
                    writeln!(
                        module,
                        "\t{w} = insertvalue {arg_t} {args}, {ft} {v}, {}",
                        arg_count + i
                    )?;
                    args = w;
                }

                let out = module.var();
                let args = if *arg_t == LLVMType::Void {
                    format!("()")
                } else {
                    format!("({arg_t} {args})")
                };

                if t == LLVMType::Void {
                    writeln!(module, "\tcall {t} {f}{args}")?; // FIX!!!
                    Ok(None)
                } else {
                    // get type of function
                    writeln!(module, "\t{out} = call {t} {f}{args}")?; // FIX!!!

                    Ok(Some(out))
                }
            }
            Self::Str(s) => {
                module.strs.push(s);
                let i = module.strs.len() - 1;

                Ok(Some(format!("@str.{i}")))
            }
            Self::Num(n) => Ok(Some(n.to_string())),
            Self::Tuple(es, t) => {
                let mut out = module.var();
                let mut es = es.into_iter();

                let e = es.next().unwrap();
                let v = e.clone().compile(module)?.unwrap();
                writeln!(
                    module,
                    "\t{out} = insertvalue {t} undef, {} {}, 0",
                    e.ty(),
                    v
                )?;

                for (i, e) in es.enumerate() {
                    let old = out;
                    out = module.var();
                    let v = e.clone().compile(module)?.unwrap();
                    writeln!(
                        module,
                        "\t{out} = insertvalue {t} {old}, {} {}, {}",
                        e.ty(),
                        v,
                        i + 1
                    )?;
                }

                Ok(Some(out))
            }
            Self::Let1(id, e, body, _) => {
                let e = e.compile(module)?;
                module.named_vars.insert(id, e.unwrap());

                body.compile(module)
            }
            Self::Unit => Ok(None),
            Self::List(es, _) => {
                let last_i = es.len() - 1;
                for i in 0..last_i {
                    es[i].clone().compile(module)?;
                }

                es[last_i].clone().compile(module)
            }
            Self::GetTuple(tup, i, _) => {
                let t = tup.ty();
                let tup = tup.compile(module)?.unwrap();
                let out = module.var();

                writeln!(module, "\t{out} = extractvalue {t} {tup}, {i}")?;

                Ok(Some(out))
            }
            Self::CheckTuple(exp, id, _) => {
                let ty = exp.ty();
                let exp = exp.compile(module)?.unwrap();

                let a = module.var();
                let out = module.var();

                writeln!(module, "\t{a} = extractvalue {ty} {exp}, 0")?;
                writeln!(module, "\t{out} = icmp eq i8 {a}, {id}")?;

                Ok(Some(out))
            }
            Self::Error(_) => {
                writeln!(module, "unreachable")?;
                Ok(Some("poison".to_string()))
            }
            Self::CastTuple(exp, ty, _) => {
                let base = ty.split(".").next().unwrap();
                let exp = exp.compile(module)?.unwrap();
                let out = module.var();

                let ptr = module.var();

                writeln!(module, "\t{ptr} = alloca %{base}")?;
                writeln!(module, "\tstore %{base} {exp}, ptr {ptr}")?;
                writeln!(module, "\t{out} = load %{ty}, ptr {ptr}")?;

                Ok(Some(out))
            }
            a => unimplemented!("{a:?}"),
        }
    }
}
