use crate::lir::{LIRExpression, LIRTree};
use std::collections::HashMap;
use std::collections::HashSet;

use crate::llvm::LLVMType;
use std::error::Error;
use std::io::Write;

pub struct Module {
    w: Box<dyn Write>,
    strs: Vec<String>,
    last_lab: String,
    thunks: HashMap<String, Option<String>>,

    // index for anonymous variables
    i: usize,
    anon: usize,
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
        Self {
            w,
            strs: Vec::new(),
            last_lab: String::new(),
            thunks: HashMap::new(),

            i: 1,
            anon: 1,
            labi: 1,
        }
    }

    pub fn var(&mut self, prefix: &str) -> String {
        if prefix == "anon" {
            self.anon += 1;
            format!("%{prefix}.{}", self.anon - 1)
        } else {
            self.i += 1;
            format!("%{prefix}.{}", self.i - 1)
        }
    }

    pub fn label(&mut self) -> String {
        self.labi += 1;
        format!("Label{}", self.labi - 1)
    }

    pub fn reset(&mut self) {
        self.i = 1;
    }

    pub fn compile(&mut self, tree: LIRTree) -> Result<(), Box<dyn Error>> {
        writeln!(self, "declare ptr @malloc(i64) nounwind")?;

        // Output extern functions
        for name in tree.external {
            let (from, to) = tree.extern_types.get(&name).unwrap();

            write!(self, "declare {to} @{name}(")?;

            for (i, f) in from.iter().enumerate() {
                let attrs = match *f {
                    LLVMType::Ptr(_) | LLVMType::Str => " nocapture",
                    _ => "",
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

        // Output imported function prototypes
        for (name, t) in tree.import_funcs {
            let (args, out) = match t {
                LLVMType::Func(a, b) => (a, b),
                _ => panic!(),
            };
            writeln!(self, "declare {out} @{name} ({args})")?;
        }

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
            writeln!(self, "define private fastcc %{name} @{name} ({t} %in) {{")?;

            let out = match t.clone() {
                LLVMType::Struct(ts) => {
                    let mut v = self.var("struct");
                    let w = self.var("input");
                    let ty = &ts[0];

                    writeln!(self, "\t{w} = extractvalue {t} %in, 0")?;
                    writeln!(self, "\t{v} = insertvalue %{name} poison, {ty} {w}, 0")?;

                    for (i, ty) in ts[1..].iter().enumerate() {
                        let old = v;
                        let w = self.var("input");
                        v = self.var("struct");

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
                let (t, structargs, need_box) = match t.clone() {
                    LLVMType::Struct(mut ts) => {
                        ts.remove(0);

                        if ts.len() == 0 {
                            (LLVMType::Void, true, vec![])
                        } else if ts.len() == 1 {
                            let (need_box, t) = match ts[0].clone() {
                                LLVMType::Ptr(a) => (true, *a),
                                a => (false, a),
                            };
                            (t, false, vec![need_box])
                        } else {
                            let mut need_box = vec![];
                            (
                                LLVMType::Struct(
                                    ts.into_iter()
                                        .map(|t| match t {
                                            LLVMType::Ptr(a) => {
                                                need_box.push(true);
                                                *a
                                            }
                                            _ => {
                                                need_box.push(false);
                                                t
                                            }
                                        })
                                        .collect(),
                                ),
                                true,
                                need_box,
                            )
                        }
                    }
                    _ => unreachable!(),
                };

                if t == LLVMType::Void {
                    writeln!(self, "define private fastcc %{name} @{varname} () {{")?;
                } else {
                    writeln!(
                        self,
                        "define private fastcc %{name} @{varname} ({t} %in) {{"
                    )?;
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
                        let v = self.var("input");
                        let i_ptr = self.var("ptr");

                        writeln!(self, "\t{v} = extractvalue {t} %in, {i}")?;

                        let (v, t2) = if need_box[i] {
                            let x = self.var("malloc");
                            let size = t2.size(0, &tree.type_sizes).unwrap() / 8;
                            writeln!(self, "\t{x} = call ptr @malloc(i32 {size})")?;
                            writeln!(self, "\tstore {t2} {v}, ptr {x}")?;
                            (x, LLVMType::Ptr(Box::new(LLVMType::Void)))
                        } else {
                            (v, t2)
                        };

                        writeln!(self, "\t{i_ptr} = getelementptr inbounds %{name}.{varname}, ptr %ptr, i32 0, i32 {}", i+1)?;
                        writeln!(self, "\tstore {t2} {v}, ptr {i_ptr}")?;
                    }
                } else {
                    if need_box[0] {
                        let x = self.var("malloc");
                        let size = t.size(0, &tree.type_sizes).unwrap() / 8;
                        writeln!(self, "\t{x} = call ptr @malloc(i32 {size})")?;

                        // get pointer to and store single value
                        writeln!(
                            self,
                            "\t%var = getelementptr inbounds %{name}.{varname}, ptr %ptr, i32 0, i32 1"
                        )?;
                        writeln!(self, "\tstore {t} %in, ptr {x}")?;
                        writeln!(self, "\tstore ptr {x}, ptr %var")?;
                    } else {
                        // get pointer to and store single value
                        writeln!(
                            self,
                            "\t%var = getelementptr inbounds %{name}.{varname}, ptr %ptr, i32 0, i32 1"
                        )?;
                        writeln!(self, "\tstore {t} %in, ptr %var")?;
                    }
                }

                writeln!(self, "\n\t%ret = load %{name}, ptr %ptr")?;
                writeln!(self, "\tret %{name} %ret")?;
                writeln!(self, "}}\n")?;
            }
        }

        // Compile all functions
        self.reset();
        let mut named_vars = HashMap::new();
        named_vars.insert("arg.0".to_string(), "%arg.0".to_string());
        for (name, expr) in tree.funcs {
            // get function type
            let (from, to) = tree.func_types.get(&name).unwrap();

            if *from == LLVMType::Void {
                writeln!(self, "define fastcc {to} @{name}() {{")?;
            } else {
                writeln!(self, "define fastcc {to} @{name}({from} %arg.0) {{")?;
            }

            let var = self.var("return");
            let var = expr.compile(self, named_vars.clone(), Some(var))?;

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
    fn compile(
        self,
        module: &mut Module,
        named_vars: HashMap<String, String>,
        out: Option<String>,
    ) -> Result<Option<String>, Box<dyn Error>> {
        match self {
            Self::If(cond, yes, no, t) => {
                let cond = cond.compile(module, named_vars.clone(), None)?.unwrap();

                let yeslab = module.label();
                let nolab = module.label();
                let endlab = module.label();

                writeln!(module, "\tbr i1 {cond}, label %{yeslab}, label %{nolab}")?;

                writeln!(module, "{}:", yeslab)?;
                module.last_lab = yeslab.clone();
                let yes = yes.compile(module, named_vars.clone(), None)?;
                let yeslab = module.last_lab.clone();
                writeln!(module, "\tbr label %{endlab}")?;

                writeln!(module, "{}:", nolab)?;
                module.last_lab = nolab.clone();

                let else_thunk = match *no {
                    LIRExpression::GotoThunk(..) => true,
                    _ => false,
                };

                let no = no.compile(module, named_vars, None)?;
                let nolab = module.last_lab.clone();

                if !else_thunk {
                    writeln!(module, "\tbr label %{endlab}")?;
                }

                writeln!(module, "{}:", endlab)?;
                module.last_lab = endlab.clone();

                if t != LLVMType::Void {
                    if else_thunk {
                        Ok(Some(yes.unwrap()))
                    } else {
                        let out = out.unwrap_or(module.var("if"));
                        writeln!(
                            module,
                            "\t{out} = phi {t} [{}, %{yeslab}], [{}, %{nolab}]",
                            yes.unwrap(),
                            no.unwrap()
                        )?;
                        Ok(Some(out))
                    }
                } else {
                    Ok(None)
                }
            }
            Self::Identifier(n, _) => {
                if let Some(v) = named_vars.get(&n) {
                    Ok(Some(v.clone()))
                } else {
                    Ok(Some(format!("@{n}")))
                }
            }
            Self::ExternCall(f, args, t) => {
                let out = out.unwrap_or(module.var("extern_call"));

                let mut a = vec![];
                let mut ts = vec![];
                for arg in args {
                    ts.push(arg.ty());
                    a.push(arg.compile(module, named_vars.clone(), None)?);
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
                    Ok(Some(out))
                } else {
                    Ok(None)
                }
            }
            Self::GlobalCall(f, args, t) => {
                let argt = args.ty();
                let args = args.compile(module, named_vars, None)?;
                let out = out.unwrap_or(module.var("global_call"));

                let args = if let Some(args) = args {
                    format!("({argt} {args})")
                } else {
                    format!("()")
                };

                if t == LLVMType::Void {
                    writeln!(module, "\tcall fastcc {t} @{f}{args}")?; // FIX!!!
                    Ok(None)
                } else {
                    // get type of function
                    writeln!(module, "\t{out} = call fastcc {t} @{f}{args}")?; // FIX!!!

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

                let closure = f.compile(module, named_vars.clone(), None)?.unwrap();

                let mut args = match arg_count {
                    0 => "poison".to_string(),
                    1 => {
                        // create a tuple
                        let tup = LIRExpression::Tuple(vec![*args], *arg_t.clone());
                        tup.compile(module, named_vars, None)?.unwrap()
                    }
                    _ => args.compile(module, named_vars, None)?.unwrap(),
                };

                let formals = match clos_t.clone() {
                    LLVMType::Struct(mut ts) => {
                        ts.remove(0);
                        ts
                    }
                    _ => panic!(),
                };

                // Get function pointer
                let f = module.var("func_ptr");
                writeln!(module, "\t{f} = extractvalue {clos_t} {closure}, 0")?;

                // insert formals into args struct
                for i in 0..formals.len() {
                    let ft = &formals[i];

                    // get the formal from the closure tuple
                    let v = module.var("formal");
                    writeln!(module, "\t{v} = extractvalue {clos_t} {closure}, {}", i + 1)?;

                    // insert into the args
                    let w = module.var("args");
                    writeln!(
                        module,
                        "\t{w} = insertvalue {arg_t} {args}, {ft} {v}, {}",
                        arg_count + i
                    )?;
                    args = w;
                }

                let out = out.unwrap_or(module.var("call"));
                let args = if *arg_t == LLVMType::Void {
                    format!("()")
                } else {
                    format!("({arg_t} {args})")
                };

                if t == LLVMType::Void {
                    writeln!(module, "\tcall fastcc {t} {f}{args}")?; // FIX!!!
                    Ok(None)
                } else {
                    // get type of function
                    writeln!(module, "\t{out} = call fastcc {t} {f}{args}")?; // FIX!!!

                    Ok(Some(out))
                }
            }
            Self::Str(s) => {
                module.strs.push(s);
                let i = module.strs.len() - 1;

                Ok(Some(format!("@str.{i}")))
            }
            Self::Num(n, _) => Ok(Some(n.to_string())),
            Self::Tuple(es, t) => {
                let mut tout = module.var("tuple");
                let len = es.len();
                let mut es = es.into_iter();

                let e = es.next().unwrap();
                let v = e
                    .clone()
                    .compile(module, named_vars.clone(), None)?
                    .unwrap();
                writeln!(
                    module,
                    "\t{tout} = insertvalue {t} poison, {} {}, 0",
                    e.ty(),
                    v
                )?;

                for (i, e) in es.enumerate() {
                    let old = tout;

                    tout = if i == len - 1 {
                        out.clone().unwrap_or(module.var("tuple"))
                    } else {
                        module.var("tuple")
                    };

                    let v = e
                        .clone()
                        .compile(module, named_vars.clone(), None)?
                        .unwrap();
                    writeln!(
                        module,
                        "\t{tout} = insertvalue {t} {old}, {} {}, {}",
                        e.ty(),
                        v,
                        i + 1
                    )?;
                }

                Ok(Some(tout))
            }
            Self::Let1(id, e, body, _) => {
                let v = module.var(&id);
                let e = e.compile(module, named_vars.clone(), Some(v))?;
                let mut named_vars = named_vars.clone();
                named_vars.insert(id, e.unwrap());

                body.compile(module, named_vars, out)
            }
            Self::Unit => Ok(None),
            Self::List(es, _) => {
                let last_i = es.len() - 1;
                for i in 0..last_i {
                    es[i].clone().compile(module, named_vars.clone(), None)?;
                }

                es[last_i].clone().compile(module, named_vars, out)
            }
            Self::GetTuple(tup, i, _) => {
                let t = tup.ty();
                let tup = tup.compile(module, named_vars, None)?.unwrap();
                let out = out.unwrap_or(module.var("gettuple"));

                writeln!(module, "\t{out} = extractvalue {t} {tup}, {i}")?;

                Ok(Some(out))
            }
            Self::CheckTuple(exp, id, _) => {
                let ty = exp.ty();
                let exp = exp.compile(module, named_vars, None)?.unwrap();

                let a = module.var("tag");
                let out = out.unwrap_or(module.var("checktuple"));

                writeln!(module, "\t{a} = extractvalue {ty} {exp}, 0")?;
                writeln!(module, "\t{out} = icmp eq i8 {a}, {id}")?;

                Ok(Some(out))
            }
            Self::Error(_) => Ok(Some("poison".to_string())),
            Self::CastTuple(exp, ty, _) => {
                let base = exp.ty();
                let exp = exp.compile(module, named_vars, None)?.unwrap();
                let out = out.unwrap_or(module.var("tuple"));

                let ptr = module.var("cast_ptr");

                writeln!(module, "\t{ptr} = alloca {base}")?;
                writeln!(module, "\tstore {base} {exp}, ptr {ptr}")?;
                writeln!(module, "\t{out} = load %{ty}, ptr {ptr}")?;

                Ok(Some(out))
            }
            Self::Unbox(e, ty) => {
                let out = out.unwrap_or(module.var("unboxed"));
                let ptr = e.compile(module, named_vars, None)?.unwrap();

                writeln!(module, "\t{out} = load {ty}, ptr {ptr}")?;
                Ok(Some(out))
            }
            Self::LLVM(out, body, _) => {
                // extract out free variables
                let mut defs = HashSet::new();
                let mut newbody = String::new();

                for line in body.lines() {
                    let line = line.trim();

                    if let Some((assn, rest)) = line.split_once('=') {
                        let assn = assn.trim();
                        if assn.starts_with("%") {
                            defs.insert(assn.to_string());
                        }

                        let rest: String = rest
                            .split(' ')
                            .map(|s| {
                                let t = s.replace(",", "");
                                if t.starts_with("%") && !defs.contains(&t) {
                                    if let Some(v) = named_vars.get(&t[1..]) {
                                        s.replace(&t, v)
                                    } else {
                                        s.to_string()
                                    }
                                } else {
                                    s.to_string()
                                }
                            })
                            .collect::<Vec<_>>()
                            .join(" ");

                        newbody.push_str(&format!("{}= {}", assn, rest));
                    } else {
                        let rest: String = line
                            .split(' ')
                            .map(|s| {
                                let t = s.replace(",", "");
                                if t.starts_with("%") && !defs.contains(&t) {
                                    if let Some(v) = named_vars.get(&t[1..]) {
                                        s.replace(&t, v)
                                    } else {
                                        s.to_string()
                                    }
                                } else {
                                    s.to_string()
                                }
                            })
                            .collect::<Vec<_>>()
                            .join(" ");

                        newbody.push_str(&format!("{}", rest));
                    }
                }

                writeln!(module, "{}", newbody)?;
                Ok(Some(out))
            }
            Self::LetThunk(thunk, expr, first, t) => {
                let void = t == LLVMType::Void;

                let afterlab = module.label();
                let firstlab = module.label();
                writeln!(module, "\tbr label %{firstlab}")?;

                writeln!(module, "{thunk}:")?;
                module.last_lab = thunk.clone();
                let thunk_out = expr.compile(module, named_vars.clone(), None)?;
                let after_thunk = module.last_lab.clone();

                writeln!(module, "\tbr label %{afterlab}")?;

                module.thunks.insert(thunk, thunk_out.clone());

                writeln!(module, "{firstlab}:")?;
                module.last_lab = firstlab.clone();
                let first_out = first.compile(module, named_vars.clone(), None)?;
                let after_first = module.last_lab.clone();
                writeln!(module, "\tbr label %{afterlab}")?;

                writeln!(module, "{afterlab}:")?;
                module.last_lab = afterlab.clone();

                if void {
                    Ok(None)
                } else {
                    let out = module.var("letthunk");
                    writeln!(
                        module,
                        "\t{out} = phi {t} [{}, %{after_first}], [{}, %{after_thunk}]",
                        first_out.unwrap(),
                        thunk_out.unwrap()
                    )?;

                    Ok(Some(out))
                }
            }
            Self::GotoThunk(thunk, _) => {
                writeln!(module, "br label %{thunk}")?;
                Ok(module.thunks[&thunk].clone())
                // Ok(Some("%wehitathunkhooray".to_string()))
            }
            a => unimplemented!("{a:?}"),
        }
    }
}
