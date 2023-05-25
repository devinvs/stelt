use std::collections::HashMap;
use std::collections::HashSet;

use crate::llvm::LLVMType;

use crate::mir::MIRExpression;
use crate::mir::MIRTree;
use crate::parse_tree::Type;
use crate::parse_tree::Pattern;

#[derive(Debug)]
pub struct LIRTree {
    /// Set of external function names
    pub external: HashSet<String>,

    /// Map of function names to their llvm types
    pub func_types: HashMap<String, (LLVMType, LLVMType)>,

    /// Map of function names to their expressions
    pub funcs: HashMap<String, LIRExpression>,
}

impl MIRTree {
    pub fn lower(self) -> LIRTree {
        let mut func_types = HashMap::new();
        let mut funcs = HashMap::new();

        // add all types of functions that we know
        for (f, t) in self.typedefs {
            let t = match t {
                Type::ForAll(_, a, _) => *a,
                a => a
            };

            if let Type::Arrow(from, to, _) = t {
                func_types.insert(f, (LLVMType::from_type(*from), LLVMType::from_type(*to)));
            } 
        }

        // lower all the mir functions to lir expressions
        for (f, expr) in self.funcs {
            funcs.insert(f, expr.lower());
        }

        // extract all the functions from the lir
        let mut extracted_funcs = HashMap::new();
        for (name, expr) in funcs {
            let (_, funcs) = expr.extract_funcs(name, 0);
            extracted_funcs.extend(funcs)
        }

        LIRTree {
            external: self.external,
            func_types,
            funcs: extracted_funcs
        }
    }
}


#[derive(Debug, PartialEq, Clone)]
pub enum LIRExpression {
    Identifier(String),

    /// Call the function with args
    /// Can be a global function, a lambda, or a constructor
    Call(Box<LIRExpression>, Box<LIRExpression>),

    Lambda1(String, Box<LIRExpression>),

    Let1(String, Box<LIRExpression>, Box<LIRExpression>),

    // Constant Fields
    Num(u64),    // A Number Literal
    Str(String), // A String Literal, stores index into constant string array
    Unit
}

impl LIRExpression {
    fn extract_funcs(self, id: String, index: usize) -> (LIRExpression, HashMap<String, LIRExpression>) {
        match self {
            Self::Lambda1(_, body) => {
                let (e, mut funcs) = body.extract_funcs(format!("{id}??{index}"), index+1);

                funcs.insert(id.clone(), e);

                (LIRExpression::Identifier(id), funcs)
            }
            Self::Call(func, args) => {
                let (e, cs) = func.extract_funcs(id, index);

                (Self::Call(Box::new(e), args), cs)
            }
            _ => (self, HashMap::new())
        }
    }
}

impl MIRExpression {
    pub fn lower(self) -> LIRExpression {
        match self {
            Self::Call(f, args, _) => LIRExpression::Call(Box::new(f.lower()), Box::new(args.lower())),
            Self::Str(s, _) => LIRExpression::Str(s),
            Self::Lambda1(arg, body, _) => LIRExpression::Lambda1(arg, Box::new(body.lower())),
            Self::Match(m, pats, _) => {
                if pats.len() == 1 {
                    // unit type always passes the pattern match
                    if let (Pattern::Unit(_), expr) = &pats[0] {
                        return expr.clone().lower();
                    }

                    if let (Pattern::Var(s, _), expr) = &pats[0] {
                        return LIRExpression::Let1(s.clone(), Box::new(m.lower()), Box::new(expr.clone().lower()))
                    }
                }

                unimplemented!("Bad match! (for now): {m:?} {pats:?}")
            }
            Self::Identifier(s, _) => LIRExpression::Identifier(s),
            Self::Num(n, _) => LIRExpression::Num(n),
            a => unimplemented!("{a:?}")
        }
    }

}
