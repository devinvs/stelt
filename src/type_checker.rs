use std::collections::HashMap;

use crate::parse_tree::Type;
use crate::unify::Theta;
use crate::unify::Term;
use crate::mir::MIRExpression as Expression;

pub type Gamma = HashMap<String, Type>;

impl Type {
    fn to_term(self) -> Term<String> {
        match self {
            // Base types
            Self::U8 => Term::Const("u8".to_string()),
            Self::U16 => Term::Const("u16".to_string()),
            Self::U32 => Term::Const("u32".to_string()),
            Self::U64 => Term::Const("u64".to_string()),
            Self::I8 => Term::Const("i8".to_string()),
            Self::I16 => Term::Const("i16".to_string()),
            Self::I32 => Term::Const("i32".to_string()),
            Self::I64 => Term::Const("i64".to_string()),
            Self::Str => Term::Const("str".to_string()),
            Self::Unit => Term::Const("()".to_string()),

            Self::List(t) => Term::Composite(
                "list".to_string(),
                vec![t.to_term()]
            ),
            Self::Generic(args, t) => {
                let name = match *t {
                    Type::Ident(s) => s,
                    _ => panic!("why would you do this to me?")
                };

                Term::Composite(
                    name,
                    args.into_iter()
                        .map(|a| a.to_term())
                        .collect()
                )
            },
            Self::Arrow(a, b) => {
                Term::Composite(
                    "->".to_string(),
                    vec![
                        a.to_term(),
                        b.to_term(),
                    ]
                )
            },
            Self::Tuple(ts) => {
                Term::Composite(
                    "tuple".to_string(),
                    ts.into_iter()
                        .map(|t| t.to_term())
                        .collect()
                )
            },
            Self::Ident(s) => {
                Term::Const(s)
            }
            Self::Var(n) => {
                Term::Var(n)
            }
            _ => panic!("plz no")
        }
    }
}


pub struct TypeChecker {
    next_var: usize,
}

// Type -> unify term
// switch forall with unify vars
// yeah

impl TypeChecker {
    fn gen_var(&mut self) -> Type {
        let t = Type::Var(self.next_var);
        self.next_var += 1;
        t
    }

    fn judge_empty_list(
        &mut self,
        e: Expression,
        t: Type,
        subs
    ) {

    }

    fn judge_type(
        &mut self,
        builtins: Gamma,
        cons: Gamma,
        defs: Gamma,
        e: Expression,
        t: Type,
        subs: Theta<Term<String>>
    ) -> Theta<Term<String>> {
        match expr {
            Expression::Unit => self.judge_unit(e, t, subs),
            Expression::EmptyList => self.judge_empty_list(e, t, subs),
            Expression::Num(_) => self.judge_num(e, t, subs),
            Expression::Str(_) => self.judge_str(e, t, subs),
            Expression::Identifier(_) => self.judge_var(builtins, cons, defs, e, t, subs),
            Expression::Tuple(_) => self.judge_tuple(builtins, cons, defs, e, t, su),
            Expression::Lambda(_, _) => {}
            Expression::Call(_, _) => {}
            Expression::Match(_, _) => {}
            _ => panic!("please don't make me go through this")
        }
    }
}
