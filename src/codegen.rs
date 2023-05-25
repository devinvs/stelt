use crate::lir::{LIRTree, LIRExpression};
use std::collections::HashMap;

use std::io::Write;
use std::error::Error;

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
        format!("%anon.{}", self.i-1)
    }

    pub fn label(&mut self) -> String {
        self.labi += 1;
        format!("Label{}", self.labi-1)
    }

    pub fn compile(&mut self, tree: LIRTree) -> Result<(), Box<dyn Error>> {
        // output builtin functions
        writeln!(self, "{}", crate::builtin::BUILTIN_ASM)?;

        // Output extern functions
        for name in tree.external {
            let (from, to) = tree.func_types.get(&name).unwrap();
            writeln!(self, "declare {to} @{name}({from} nocapture) nounwind")?;
        }

        // Compile all functions
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
                writeln!(self, "\tret {to} {var}")?;
            }

            writeln!(self, "}}")?;
        }

        // Emit string definitions
        for (i, s) in self.strs.clone().into_iter().enumerate() {
            let len = s.len() + 1; // plus one because null byte
            let s = s.replace("\n", "\\0a");

            writeln!(self, "@str.{i} = private unnamed_addr constant [{len} x i8] c\"{s}\\00\"")?;
        }

        Ok(())
    }
}

impl LIRExpression {
    fn compile(self, module: &mut Module) -> Result<String, Box<dyn Error>> {
        match self {
            Self::If(cond, yes, no, t) => {
                let out = module.var();
                writeln!(module, "\t{out} = alloca {t}")?;

                let cond = cond.compile(module)?;

                let yeslab = module.label();
                let nolab = module.label();
                let endlab = module.label();

                writeln!(module, "\tbr i1 {cond}, label %{yeslab}, label %{nolab}")?;
                
                writeln!(module, "{}:", yeslab)?;
                let yesout = yes.compile(module)?;
                writeln!(module, "\tstore {t} {yesout}, ptr {out}")?;
                writeln!(module, "\tbr label %{endlab}")?;

                writeln!(module, "{}:", nolab)?;
                let noout = no.compile(module)?;
                writeln!(module, "\tstore {t} {noout}, ptr {out}")?;
                writeln!(module, "\tbr label %{endlab}")?;

                writeln!(module, "{}:", endlab)?;
                let fin = module.var();
                writeln!(module, "\t{fin} = load {t}, ptr {out}")?;

                Ok(fin)
            }
            Self::Identifier(n, _) => {
                if let Some(var) = module.named_vars.get(&n) {
                    Ok(var.clone())
                } else {
                    Ok(format!("@{n}"))
                }
            }
            Self::Call(f, args, t) => {
                let argt = args.ty();
                let args = args.compile(module)?;
                let f = f.compile(module)?;
                let out = module.var();

                // get type of function
                writeln!(module, "\t{out} = call {t} {f}({argt} {args})")?; // FIX!!!

                Ok(out)
            }
            Self::Str(s) => {
                module.strs.push(s);
                let i = module.strs.len() - 1;

                Ok(format!("@str.{i}"))
            }
            Self::Num(n) => {
                Ok(n.to_string())
            }
            Self::Tuple(es, t) => {
                let mut out = module.var();
                let mut es = es.into_iter();

                let e = es.next().unwrap();
                let v = e.clone().compile(module)?;
                writeln!(module, "\t{out} = insertvalue {t} undef, {} {}, 0", e.ty(), v)?;

                for (i, e) in es.enumerate() {
                    let old = out;
                    out = module.var();
                    let v = e.clone().compile(module)?;
                    writeln!(module, "\t{out} = insertvalue {t} {old}, {} {}, {}", e.ty(), v, i+1)?;
                }

                Ok(out)
            }
            Self::Let1(id, e, body, _) => {
                let e = e.compile(module)?;
                module.named_vars.insert(id, e);

                body.compile(module)
            }
            a => unimplemented!("{a:?}")
        }
    }
}
