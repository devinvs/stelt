use crate::lir::{LIRTree, LIRExpression};

use std::io::Write;
use std::error::Error;

use crate::llvm::LLVMType;

pub struct Module {
    w: Box<dyn Write>,
    strs: Vec<String>,

    // index for anonymous variables
    i: usize,
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

            i: 1,
        }
    }

    pub fn var(&mut self) -> String {
        self.i += 1;
        format!("%{}", self.i-1)
    }

    pub fn compile(&mut self, tree: LIRTree) -> Result<(), Box<dyn Error>> {
        // Output extern functions
        for name in tree.external {
            let (from, to) = tree.func_types.get(&name).unwrap();
            writeln!(self, "declare {to} @{name}({from} nocapture) nounwind")?;
        }

        // Compile all functions
        for (name, expr) in tree.funcs {
            // get function type
            let (from, to) = tree.func_types.get(&name).unwrap();

            let froms = if *from == LLVMType::Void { "".to_string() } else { format!("{from}") };

            writeln!(self, "define {to} @{name}({froms}) {{")?;

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
            Self::Identifier(n) => {
                // for now just assume its a function...
                Ok(format!("@{n}"))
            }
            Self::Call(f, args) => {
                let args = args.compile(module)?;
                let f = f.compile(module)?;
                let out = module.var();

                // get type of function

                writeln!(module, "\t{out} = call i32 {f}(ptr {args})")?; // FIX!!!

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
            a => unimplemented!("{a:?}")
        }
    }
}
