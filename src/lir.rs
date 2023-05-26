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
                Type::ForAll(_, a) => *a,
                a => a
            };

            if let Type::Arrow(from, to) = t {
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
    Identifier(String, LLVMType),

    /// Call the function with args
    /// Can be a global function, a lambda, or a constructor
    Call(Box<LIRExpression>, Box<LIRExpression>, LLVMType),

    Lambda1(String, Box<LIRExpression>, LLVMType),

    Let1(String, Box<LIRExpression>, Box<LIRExpression>, LLVMType),

    If(Box<LIRExpression>, Box<LIRExpression>, Box<LIRExpression>, LLVMType),

    List(Vec<LIRExpression>, LLVMType),

    // Constant Fields
    Num(u64),    // A Number Literal
    Str(String), // A String Literal, stores index into constant string array
    Unit,
    Tuple(Vec<LIRExpression>, LLVMType),

    Error(String)
}

impl LIRExpression {
    fn extract_funcs(self, id: String, index: usize) -> (LIRExpression, HashMap<String, LIRExpression>) {
        match self {
            Self::Lambda1(_, body, t) => {
                let (e, mut funcs) = body.extract_funcs(format!("{id}??{index}"), index+1);

                funcs.insert(id.clone(), e);

                (LIRExpression::Identifier(id, t), funcs)
            }
            Self::Call(func, args, t) => {
                let (e, cs) = func.extract_funcs(id, index);

                (Self::Call(Box::new(e), args, t), cs)
            }
            _ => (self, HashMap::new())
        }
    }

    pub fn ty(&self) -> LLVMType {
        match self {
            Self::Unit => LLVMType::Void,
            Self::Call(_, _, t) => t.clone(),
            Self::Error(_) => LLVMType::Void,
            Self::Identifier(_, t) => t.clone(),
            Self::Lambda1(_, _, t) => t.clone(),
            Self::Str(..) => LLVMType::Ptr,
            Self::Let1(_, _, _, t) => t.clone(),
            Self::If(_, _, _, t) => t.clone(),
            Self::Num(_) => LLVMType::I32,
            Self::Tuple(_, t) => t.clone(),
            Self::List(_, t) => t.clone(),
        }
    }
}

impl MIRExpression {
    pub fn lower(self) -> LIRExpression {
        match self {
            Self::Call(f, args, _, t) => LIRExpression::Call(Box::new(f.lower()), Box::new(args.lower()), LLVMType::from_type(t.unwrap())),
            Self::Str(s, _, _) => LIRExpression::Str(s),
            Self::Lambda1(arg, body, _, t) => LIRExpression::Lambda1(arg, Box::new(body.lower()), LLVMType::from_type(t.unwrap())),
            Self::Match(m, pats, _, t) => {
                if pats.len() == 1 {
                    // unit type always passes the pattern match
                    if let (Pattern::Unit(..), expr) = &pats[0] {
                        return expr.clone().lower();
                    }

                    // Single var pattern just becomes a let expression
                    if let (Pattern::Var(s, _, t2), expr) = &pats[0] {
                        return LIRExpression::Let1(s.clone(), Box::new(m.lower()), Box::new(expr.clone().lower()), LLVMType::from_type(t2.clone().unwrap()))
                    }

                }

                // transform if statements
                // TODO

                // General case
                if let Self::Identifier(n, _, _) = *m {
                    Self::match_code(n, &pats, LLVMType::from_type(t.unwrap()))
                } else {
                    let n = "ahahahah".to_string(); // TODO: generate real variable
                    LIRExpression::Let1(n.clone(), Box::new(m.lower()), Box::new(Self::match_code(n, &pats, LLVMType::from_type(t.clone().unwrap()))), LLVMType::from_type(t.unwrap()))
                }
            }
            Self::Identifier(s, _, t) => LIRExpression::Identifier(s, LLVMType::from_type(t.unwrap())),
            Self::Num(n, _, _) => LIRExpression::Num(n),
            Self::Tuple(es, _, t) => LIRExpression::Tuple(es.into_iter().map(|e| e.lower()).collect(), LLVMType::from_type(t.unwrap())),
            Self::List(es, _, t) => LIRExpression::List(es.into_iter().map(|e| e.lower()).collect(), LLVMType::from_type(t.unwrap())),
            Self::Unit(_, _) => LIRExpression::Unit,
            a => unimplemented!("{a:?}")
        }
    }

    fn match_code(x: String, pats: &[(Pattern, MIRExpression)], ty: LLVMType) -> LIRExpression {
        if pats.is_empty() {
            LIRExpression::Error("No patterns matched".to_string())
        } else {
            let fail = Self::match_code(x.clone(), &pats[1..], ty.clone());
            let (pat, exp) = &pats[0];

            Self::match_pattern(
                pat.clone(),
                LIRExpression::Identifier(x, LLVMType::from_type(pat.ty())),
                exp.clone().lower(),
                fail,
                ty
            )
        }
    }

    fn match_pattern(pat: Pattern, exp: LIRExpression, yes: LIRExpression, no: LIRExpression, ty: LLVMType) -> LIRExpression {
        match pat {
            Pattern::Num(n, _, _) => {
                LIRExpression::If(
                    Box::new(LIRExpression::Call(
                        Box::new(LIRExpression::Identifier(
                            "eq".into(),
                            LLVMType::Ptr
                        )), 
                        Box::new(LIRExpression::Tuple(vec![
                            exp,
                            LIRExpression::Num(n),
                        ], LLVMType::Struct(vec![LLVMType::I32, LLVMType::I32]))),
                        LLVMType::I1
                    )),
                    Box::new(yes),
                    Box::new(no),
                    ty
                )
            },
            Pattern::Var(x, _, t) => {
                LIRExpression::Let1(x, Box::new(exp), Box::new(yes), LLVMType::from_type(t.unwrap()))
            }
            a => unimplemented!("{a:?}")
        }
    }
}

