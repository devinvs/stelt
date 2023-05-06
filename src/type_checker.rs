use std::collections::HashMap;
use std::collections::HashSet;

use crate::parse_tree::{Type, Pattern};
use crate::unify::Term;
use crate::unify::unify;
use crate::unify::apply_unifier;
use crate::mir::MIRExpression as Expression;
use crate::error::Range;
use crate::error::SteltError;

use crate::mir::MIRTree;

type Theta = HashMap<Term<String>, Term<String>>;
type Gamma<'a> = &'a HashMap<String, Type>;
type MutGamma<'a> = &'a mut HashMap<String, Type>;

const R0: Range = Range::line(0, 0, 0);

impl Type {
    fn to_term(&self) -> Term<String> {
        match self {
            // Base types
            Self::U8(_) => Term::Const("u8".to_string()),
            Self::U16(_) => Term::Const("u16".to_string()),
            Self::U32(_) => Term::Const("u32".to_string()),
            Self::U64(_) => Term::Const("u64".to_string()),
            Self::I8(_) => Term::Const("i8".to_string()),
            Self::I16(_) => Term::Const("i16".to_string()),
            Self::I32(_) => Term::Const("i32".to_string()),
            Self::I64(_) => Term::Const("i64".to_string()),
            Self::Str(_) => Term::Const("str".to_string()),
            Self::Unit(_) => Term::Const("()".to_string()),

            Self::List(t, _) => Term::Composite(
                "list".to_string(),
                vec![t.to_term()]
            ),
            Self::Generic(args, t, _) => {
                let name = match &**t {
                    Type::Ident(s, _) => s.clone(),
                    _ => panic!("why would you do this to me?")
                };

                Term::Composite(
                    name,
                    args.into_iter()
                        .map(|a| a.to_term())
                        .collect()
                )
            },
            Self::Arrow(a, b, _) => {
                Term::Composite(
                    "->".to_string(),
                    vec![
                        a.to_term(),
                        b.to_term(),
                    ]
                )
            },
            Self::Tuple(ts, _) => {
                Term::Composite(
                    "tuple".to_string(),
                    ts.into_iter()
                        .map(|t| t.to_term())
                        .collect()
                )
            },
            Self::Ident(s, _) => {
                Term::Const(s.clone())
            }
            Self::Var(n) => {
                Term::Var(*n)
            }
            _ => panic!("plz no")
        }
    }

    fn map(&self, m: &HashMap<String, Type>) -> Self {
        match self {
            Self::Ident(s, _) => m.get(s).unwrap_or(&self).clone(),
            Self::Tuple(ts, r) => Self::Tuple(
                ts.into_iter()
                .map(|t| t.map(m))
                .collect(),
                r.clone()
            ),
            Self::Arrow(a, b, r) => Self::Arrow(Box::new(a.map(m)), Box::new(b.map(m)), r.clone()),
            Self::List(a, r) => Self::List(Box::new(a.map(m)), r.clone()),
            Self::Generic(vars, a, r) => Self::Generic(
                vars.into_iter().map(|t| t.map(m)).collect(),
                Box::new(a.map(m)),
                r.clone()
            ),
            _ => self.clone()
        }
    }
}

#[derive(Default)]
pub struct TypeChecker {
    next_var: usize,
}

// Type -> unify term
// switch forall with unify vars
// yeah

impl TypeChecker {
    pub fn check_program(&mut self, tree: &MIRTree) -> Result<(), SteltError> {
        // Check all defs
        for (name, def) in tree.defs.iter() {
            let ty = tree.declarations.get(name).unwrap().clone();
            self.check_expression(
                &tree.builtins,
                &tree.constructors,
                &tree.declarations,
                def.clone(),
                ty.clone()
            )?;
        }

        // Check all functions
        for (name, func) in tree.funcs.iter() {
            let ty = tree.declarations.get(name).unwrap().clone();
            self.check_expression(
                &tree.builtins,
                &tree.constructors,
                &tree.declarations,
                func.clone(),
                ty.clone()
            )?;
        }

        Ok(())
    }

    fn check_expression(&mut self, b: Gamma, c: Gamma, d: Gamma, e: Expression, t: Type) -> Result<Theta, SteltError> {
        let simple = match t {
            Type::ForAll(_, t, _) => *t,
            _ => t.clone(),
        };

        self.judge_type(b, c, d, e, simple, HashMap::new())
    }

    fn gen_var(&mut self) -> Type {
        let t = Type::Var(self.next_var);
        self.next_var += 1;
        t
    }

    fn gen_fresh_type(&mut self, t: &Type) -> Type {
        match t {
            Type::ForAll(vars, inner, _) => {
                let mut m = HashMap::new();
                for v in vars {
                    m.insert(v.clone(), self.gen_var());
                }

                inner.map(&m)
            }
            a => a.clone()
        }
    }

    fn apply_gamma(&mut self, n: &String, g: Gamma) -> Option<Type> {
        g.get(n).map(|t| self.gen_fresh_type(t))
    }

    fn apply_gamma_all(&mut self, n: &String, b: Gamma, c: Gamma, d: Gamma) -> Option<Type> {
        match (b.get(n), c.get(n), d.get(n)) {
            (Some(t), _, _) => Some(t),
            (_, Some(t), _) => Some(t),
            (_, _, Some(t)) => Some(t),
            _ => None
        }.map(|t| self.gen_fresh_type(t))
    }

    fn judge_unit(&mut self, r: Range, t: Type, subs: Theta) -> Result<Theta, SteltError> {
        let tname = apply_unifier(t.to_term(), &subs).name();
        unify(Type::Unit(R0).to_term(), t.to_term(), subs).ok_or(SteltError {
            range: Some(r),
            msg: format!("Type Mismatch: Expected () found {:?}", tname)
        })
    }

    fn judge_num(&mut self, r: Range, t: Type, subs: Theta) -> Result<Theta, SteltError> {
        let tname = apply_unifier(t.to_term(), &subs).name();
        unify(Type::U64(R0).to_term(), t.to_term(), subs).ok_or(SteltError {
            range: Some(r),
            msg: format!("Type Mismatch: Expected u64 found {:?}", tname)
        })
    }

    fn judge_str(&mut self, r: Range, t: Type, subs: Theta) -> Result<Theta, SteltError> {
        let tname = apply_unifier(t.to_term(), &subs).name();
        unify(Type::Str(R0).to_term(), t.to_term(), subs).ok_or(SteltError {
            range: Some(r),
            msg: format!("Type Mismatch: Expected str found {:?}", tname)
        })
    }

    fn judge_empty_list(&mut self, r: Range, t: Type, subs: Theta) -> Result<Theta, SteltError> {
        let tname = apply_unifier(t.to_term(), &subs).name();
        let v = self.gen_var();
        unify(Type::List(Box::new(v), R0).to_term(), t.to_term(), subs).ok_or(SteltError {
            range: Some(r),
            msg: format!("Type Mismatch: Expected [] found {:?}", tname)
        })
    }

    fn judge_var(
        &mut self,
        builtins: Gamma,
        cons: Gamma,
        defined: Gamma,
        e: Expression,
        t: Type,
        subs: Theta
    ) -> Result<Theta, SteltError> {
        let r = e.range();
        let name = match e { Expression::Identifier(a, _) => a, _ => panic!() };
        let x = self.apply_gamma_all(&name, builtins, cons, defined).ok_or(SteltError {
            range: Some(r),
            msg: format!("Type not known for {name:?}")
        })?;

        let tname = apply_unifier(t.to_term(), &subs).name();
        let xname = apply_unifier(x.to_term(), &subs).name();

        unify(x.to_term(), t.to_term(), subs).ok_or(SteltError {
            range: Some(r),
            msg: format!("Type Mismatch: Expected {:?} found {:?}", xname, tname)
        })
    }

    fn judge_tuple(
        &mut self,
        b: Gamma,
        c: Gamma,
        d: Gamma,
        e: Expression,
        t: Type,
        mut subs: Theta
    ) -> Result<Theta, SteltError> {
        let mut ts = vec![];
        let r = e.range();
        match e {
            Expression::Tuple(es, _) => {
                for exp in es {
                    let tv = self.gen_var();
                    subs = self.judge_type(b, c, d, exp, tv.clone(), subs)?;
                    ts.push(tv);
                }
            }
            _ => panic!()
        }

        let tname = apply_unifier(t.to_term(), &subs).name();
        let xname = apply_unifier(Type::Tuple(ts.clone(), R0).to_term(), &subs).name();

        unify(Type::Tuple(ts, R0).to_term(), t.to_term(), subs).ok_or(SteltError {
            range: Some(r),
            msg: format!("Type Mismatch: Expected {:?} found {:?}", xname, tname)
        })
    }

    fn judge_lambda(
        &mut self,
        b: Gamma,
        c: Gamma,
        d: Gamma,
        e: Expression,
        ty: Type,
        mut subs: Theta
    ) -> Result<Theta, SteltError> {
        let t1 = self.gen_var();
        let t2 = self.gen_var();
        let r = e.range();

        let (x, m) = match e {
            Expression::Lambda1(x, m, _) => (x, m),
            _ => unreachable!()
        };

        let mut d = d.clone();
        d.insert(x, t1.clone());

        subs = self.judge_type(b, c, &d, *m, t2.clone(), subs)?;

        let tname = apply_unifier(ty.to_term(), &subs).name();
        let xname = apply_unifier(Type::Arrow(Box::new(t1.clone()), Box::new(t2.clone()), R0).to_term(), &subs).name();

        unify(Type::Arrow(Box::new(t1), Box::new(t2), R0).to_term(), ty.to_term(), subs).ok_or(SteltError {
            range: Some(r),
            msg: format!("Type Mismatch: Expected {:?} found {:?}", tname, xname)
        })
    }

    fn judge_call(
        &mut self,
        b: Gamma,
        c: Gamma,
        d: Gamma,
        e: Expression,
        ty: Type,
        mut subs: Theta
    ) -> Result<Theta, SteltError> {
        let (m, n) = match e {
            Expression::Call(m, n, _) => (m, n),
            _ => panic!()
        };
        let t = self.gen_var();
        let call_t = Type::Arrow(Box::new(t.clone()), Box::new(ty), R0);
        subs = self.judge_type(b, c, d, *n, t, subs)?;
        self.judge_type(b, c, d, *m, call_t, subs)
    }

    fn judge_match(
        &mut self,
        b: Gamma,
        c: Gamma,
        d: Gamma,
        e: Expression,
        t: Type,
        mut subs: Theta
    ) -> Result<Theta, SteltError> {
        let (mat, cases) = match e {
            Expression::Match(m, c, _) => (m, c),
            _ => panic!()
        };

        let m_type = self.gen_var();
        subs = self.judge_type(b, c, d, *mat, m_type.clone(), subs)?;

        for (pat, exp) in cases {
            let mut newd = d.clone();
            subs = self.judge_pattern(c, &mut newd, pat, m_type.clone(), subs)?;

            subs = self.judge_type(b, c, &newd, exp, t.clone(), subs)?;
        }

        Ok(subs)
    }

    fn judge_type(
        &mut self,
        builtins: Gamma,
        cons: Gamma,
        defs: Gamma,
        e: Expression,
        t: Type,
        subs: Theta
    ) -> Result<Theta, SteltError> {
        match e {
            Expression::Unit(_) => self.judge_unit(e.range(), t, subs),
            Expression::Num(_, _) => self.judge_num(e.range(), t, subs),
            Expression::Str(_, _) => self.judge_str(e.range(), t, subs),
            Expression::EmptyList(_) => self.judge_empty_list(e.range(), t, subs),
            Expression::Identifier(_, _) => self.judge_var(builtins, cons, defs, e, t, subs),
            Expression::Tuple(_, _) => self.judge_tuple(builtins, cons, defs, e, t, subs),
            Expression::Lambda1(_, _, _) => self.judge_lambda(builtins, cons, defs, e, t, subs),
            Expression::Call(_, _, _) => self.judge_call(builtins, cons, defs, e, t, subs),
            Expression::Match(_, _, _) => self.judge_match(builtins, cons, defs, e, t, subs),
            _ => panic!("please don't make me go through this")
        }
    }

    fn judge_pattern_var(
        &mut self,
        d: Gamma,
        p: Pattern,
        t: Type,
        subs: Theta
    ) -> Result<Theta, SteltError> {
        let r = p.range();
        let x = match p {
            Pattern::Var(x, _) => x,
            _ => panic!()
        };


        let x = self.apply_gamma(&x, d).unwrap();

        let tname = apply_unifier(t.to_term(), &subs).name();
        let xname = apply_unifier(x.to_term(), &subs).name();

        unify(x.to_term(), t.to_term(), subs).ok_or(SteltError {
            range: Some(r),
            msg: format!("Type Mismatch: Expected {:?} found {:?}", xname, tname)
        })
    }

    fn judge_pattern_tuple(
        &mut self,
        c: Gamma,
        d: Gamma,
        p: Pattern,
        t: Type,
        mut subs: Theta
    ) -> Result<Theta, SteltError> {
        let mut ts = vec![];
        let r = p.range();
        let ps = match p {
            Pattern::Tuple(es, _) => es,
            _ => panic!()
        };

        for pat in ps {
            let ty = self.gen_var();
            ts.push(ty.clone());
            subs = self.judge_pattern_helper(c, d, pat, ty, subs)?;
        }

        let tname = apply_unifier(t.to_term(), &subs).name();
        let xname = apply_unifier(Type::Tuple(ts.clone(), R0).to_term(), &subs).name();

        unify(Type::Tuple(ts, R0).to_term(), t.to_term(), subs).ok_or(SteltError {
            range: Some(r),
            msg: format!("Type Mismatch: Expected {:?} found {:?}", xname, tname)
        })
    }

    fn judge_pattern_cons(
        &mut self,
        c: Gamma,
        d: Gamma,
        p: Pattern,
        t: Type,
        mut subs: Theta
    ) -> Result<Theta, SteltError> {
        let (m, n) = match p {
            Pattern::Cons(m, n, _) => (m, n),
            _ => panic!()
        };

        let newt = self.gen_var();
        subs = self.judge_type(
            &HashMap::new(),
            c,
            &HashMap::new(),
            Expression::Identifier(m, R0),
            Type::Arrow(Box::new(newt.clone()), Box::new(t), R0),
            subs
        )?;

        self.judge_pattern_helper(c, d, *n, newt, subs)
    }

    fn judge_pattern_helper(
        &mut self,
        c: Gamma,
        d: Gamma,
        p: Pattern,
        t: Type,
        subs: Theta
    ) -> Result<Theta, SteltError> {
        match p {
            Pattern::Unit(_) => self.judge_unit(p.range(), t, subs),
            Pattern::Num(_, _) => self.judge_num(p.range(), t, subs),
            Pattern::Str(_, _) => self.judge_str(p.range(), t, subs),
            Pattern::EmptyList(_) => self.judge_empty_list(p.range(), t, subs),
            Pattern::Var(_, _) => self.judge_pattern_var(d, p, t, subs),
            Pattern::Tuple(_, _) => self.judge_pattern_tuple(c, d, p, t, subs),
            Pattern::Cons(_, _, _) => self.judge_pattern_cons(c, d, p, t, subs),
        }
    }

    fn judge_pattern(
        &mut self,
        c: Gamma,
        d: MutGamma,
        p: Pattern,
        t: Type,
        subs: Theta
    ) -> Result<Theta, SteltError> {
        let vars = p.free_vars();

        // check that there are no duplicate vars
        {
            let mut m = HashSet::new();
            for v in vars.iter() { m.insert(v); }

            if m.len() != vars.len() {
                return Err(SteltError {
                    range: Some(p.range()),
                    msg: "Duplicate Variables in pattern".to_string(),
                })
            }
        }

        // Add all the vars to dec2 with new type variables
        for v in vars {
            d.insert(v, self.gen_var());
        }

        self.judge_pattern_helper(c, d, p, t, subs)
    }
}
