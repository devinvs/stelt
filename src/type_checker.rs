use std::collections::HashMap;
use std::collections::HashSet;

use crate::mir::MIRExpression as Expression;
use crate::parse_tree::{Pattern, Type};
use crate::unify::apply_unifier;
use crate::unify::unify;
use crate::unify::Term;

use crate::mir::MIRTree;

type Theta = HashMap<Term<String>, Term<String>>;
type Gamma<'a> = &'a HashMap<String, Type>;
type GammaStruct<'a> = &'a HashMap<String, HashMap<String, Type>>;
type MutGamma<'a> = &'a mut HashMap<String, Type>;

impl Type {
    pub fn to_term(&self) -> Term<String> {
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
            Self::Unit => Term::Const("()".to_string()),
            Self::Generic(args, t) => {
                let mut v = vec![t.to_term()];
                v.extend(args.iter().map(|a| a.to_term()));

                Term::Composite("generic".to_string(), v)
            }
            Self::Arrow(a, b) => Term::Composite("->".to_string(), vec![a.to_term(), b.to_term()]),
            Self::Tuple(ts) => Term::Composite(
                "tuple".to_string(),
                ts.into_iter().map(|t| t.to_term()).collect(),
            ),
            Self::Ident(s) if s == "p" => panic!(),
            Self::Ident(s) => Term::Const(s.clone()),
            Self::Var(n) => Term::Var(*n),
            Self::NumVar(n) => Term::Number(*n),
            _ => panic!("plz no"),
        }
    }

    pub fn from_term(t: Term<String>) -> Self {
        match t {
            // Base const types
            Term::Const(a) if a == "u8" => Self::U8,
            Term::Const(a) if a == "u16" => Self::U16,
            Term::Const(a) if a == "u32" => Self::U32,
            Term::Const(a) if a == "u64" => Self::U64,
            Term::Const(a) if a == "i8" => Self::I8,
            Term::Const(a) if a == "i16" => Self::I16,
            Term::Const(a) if a == "i32" => Self::I32,
            Term::Const(a) if a == "i64" => Self::I64,
            Term::Const(a) if a == "()" => Self::Unit,
            Term::Const(a) => Self::Ident(a),

            // Composite types
            Term::Composite(a, b) if a == "tuple" => {
                Self::Tuple(b.into_iter().map(|t| Type::from_term(t)).collect())
            }
            Term::Composite(a, b) if a == "->" => Self::Arrow(
                Box::new(Type::from_term(b[0].clone())),
                Box::new(Type::from_term(b[1].clone())),
            ),
            Term::Composite(a, b) if a == "generic" => Self::Generic(
                b.iter().map(|t| Type::from_term(t.clone())).collect(),
                Box::new(Type::from_term(b[0].clone())),
            ),

            // Var...
            Term::Var(i) => Self::Var(i),
            Term::Number(i) => Self::NumVar(i),
            _ => panic!(),
        }
    }

    pub fn map(&self, m: &HashMap<String, Type>) -> Self {
        match self {
            Self::Ident(s) => m.get(s).unwrap_or(&self).clone(),
            Self::Tuple(ts) => Self::Tuple(ts.into_iter().map(|t| t.map(m)).collect()),
            Self::Arrow(a, b) => Self::Arrow(Box::new(a.map(m)), Box::new(b.map(m))),
            Self::Generic(vars, a) => Self::Generic(
                vars.into_iter().map(|t| t.map(m)).collect(),
                Box::new(a.map(m)),
            ),
            Self::Box(t) => Self::Box(Box::new(t.map(m))),
            _ => self.clone(),
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
    pub fn check_program(&mut self, tree: &mut MIRTree) -> Result<(), String> {
        let mut builtins = HashMap::new();
        builtins.insert(
            "llvm!".to_string(),
            Type::ForAll(
                vec!["a".to_string()],
                Box::new(Type::Arrow(
                    Box::new(Type::Tuple(vec![
                        Type::Generic(vec![Type::U32], Box::new(Type::Ident("list".to_string()))),
                        Type::Generic(vec![Type::U32], Box::new(Type::Ident("list".to_string()))),
                    ])),
                    Box::new(Type::Ident("a".to_string())),
                )),
            ),
        );

        // Check all defs
        for (name, def) in tree.defs.iter_mut() {
            // Don't type check imported functions
            let ty = self.apply_gamma(name, &tree.declarations).unwrap();
            let subs = self.check_expression(
                &builtins,
                &tree.constructors,
                &tree.declarations,
                &tree.structs,
                def,
                ty.clone(),
            )?;
            def.apply(&subs)
        }

        // Check all functions
        for (name, func) in tree.funcs.iter_mut() {
            let ty = self.apply_gamma(name, &tree.declarations).unwrap();

            let subs = self.check_expression(
                &builtins,
                &tree.constructors,
                &tree.declarations,
                &tree.structs,
                func,
                ty.clone(),
            )?;
            func.apply(&subs)
        }

        Ok(())
    }

    fn check_expression(
        &mut self,
        b: Gamma,
        c: Gamma,
        d: Gamma,
        s: GammaStruct,
        e: &mut Expression,
        t: Type,
    ) -> Result<Theta, String> {
        let simple = match t {
            Type::ForAll(_, t) => *t,
            _ => t.clone(),
        };

        let subs = self.judge_type(b, c, d, s, e, simple.clone(), HashMap::new())?;
        Ok(subs)
    }

    fn gen_var(&mut self) -> Type {
        let t = Type::Var(self.next_var);
        self.next_var += 1;
        t
    }

    fn gen_num_var(&mut self) -> Type {
        let t = Type::NumVar(self.next_var);
        self.next_var += 1;
        t
    }

    fn gen_fresh_type(&mut self, t: &Type) -> Type {
        match t {
            Type::ForAll(vars, inner) => {
                let mut m = HashMap::new();
                for v in vars {
                    m.insert(v.clone(), self.gen_var());
                }

                inner.map(&m)
            }
            a => a.clone(),
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
            _ => None,
        }
        .map(|t| self.gen_fresh_type(t))
    }

    fn judge_unit(&mut self, t: Type, subs: Theta) -> Result<Theta, String> {
        let tname = apply_unifier(t.to_term(), &subs).name();
        unify(Type::Unit.to_term(), t.to_term(), subs)
            .ok_or(format!("Type Mismatch: Expected () found {:?}", tname))
    }

    fn judge_num(&mut self, e: &mut Expression, t: Type, subs: Theta) -> Result<Theta, String> {
        let tname = apply_unifier(t.to_term(), &subs).name();
        let v = self.gen_num_var();
        e.set_type(v.clone());
        unify(v.to_term(), t.to_term(), subs)
            .ok_or(format!("Type Mismatch: Expected {v:?} found {:?}", tname))
    }

    fn judge_var(
        &mut self,
        builtins: Gamma,
        cons: Gamma,
        defined: Gamma,
        e: &mut Expression,
        t: Type,
        subs: Theta,
    ) -> Result<Theta, String> {
        let name = match e {
            Expression::Identifier(a, None) => a,
            _ => panic!(),
        };
        let x = self
            .apply_gamma_all(&name, builtins, cons, defined)
            .ok_or(format!("judge_var: Type not known for {name:?}"))?;

        let tname = apply_unifier(t.to_term(), &subs);
        let xname = apply_unifier(x.to_term(), &subs);

        let theta = unify(x.to_term(), t.to_term(), subs.clone()).ok_or(format!(
            "Type Mismatch: Expected {:?} found {:?}\n{:?}\n{:?}",
            xname, tname, name, &subs
        ))?;

        e.set_type(t);

        Ok(theta)
    }

    fn judge_tuple(
        &mut self,
        b: Gamma,
        c: Gamma,
        d: Gamma,
        s: GammaStruct,
        e: &mut Expression,
        t: Type,
        mut subs: Theta,
    ) -> Result<Theta, String> {
        let mut ts = vec![];
        match e {
            Expression::Tuple(es, _) => {
                for exp in es {
                    let tv = self.gen_var();
                    subs = self.judge_type(b, c, d, s, exp, tv.clone(), subs)?;
                    ts.push(tv);
                }
            }
            _ => panic!(),
        }

        let tname = apply_unifier(t.to_term(), &subs).name();
        let xname = apply_unifier(Type::Tuple(ts.clone()).to_term(), &subs).name();

        let subs = unify(Type::Tuple(ts).to_term(), t.to_term(), subs).ok_or(format!(
            "Type Mismatch: Expected {:?} found {:?}",
            xname, tname
        ))?;

        e.set_type(t);

        Ok(subs)
    }

    fn judge_lambda(
        &mut self,
        b: Gamma,
        c: Gamma,
        d: Gamma,
        s: GammaStruct,
        e: &mut Expression,
        ty: Type,
        mut subs: Theta,
    ) -> Result<Theta, String> {
        let t1 = self.gen_var();
        let t2 = self.gen_var();

        let (x, m) = match e {
            Expression::Lambda1(x, m, _) => (x, m),
            _ => unreachable!(),
        };

        let mut d = d.clone();
        if let Some(x) = x {
            d.insert(x.clone(), t1.clone());
        }

        // unify t1 with lambda arg type first so that struct resolution can work
        subs = match ty.clone() {
            Type::Arrow(a, _) => {
                unify(a.to_term(), t1.to_term(), subs).ok_or(format!("Type check failed here"))?
            }
            _ => subs,
            /*
            a => {
                return Err(String {
                    range: Some(r),
                    msg: format!("Expected lambda found {:?}", a)
                })
            }*/
        };

        subs = self.judge_type(b, c, &d, s, m, t2.clone(), subs)?;

        let tname = apply_unifier(ty.to_term(), &subs).name();
        let xname = apply_unifier(
            Type::Arrow(Box::new(t1.clone()), Box::new(t2.clone())).to_term(),
            &subs,
        )
        .name();

        let subs = unify(
            Type::Arrow(Box::new(t1), Box::new(t2.clone())).to_term(),
            ty.to_term(),
            subs,
        )
        .ok_or(format!(
            "Type Mismatch: Expected {:?} found {:?}\n{:?}",
            tname, xname, m
        ))?;

        m.set_type(t2);
        e.set_type(ty);

        Ok(subs)
    }

    fn judge_call(
        &mut self,
        b: Gamma,
        c: Gamma,
        d: Gamma,
        s: GammaStruct,
        e: &mut Expression,
        ty: Type,
        mut subs: Theta,
    ) -> Result<Theta, String> {
        let (m, n) = match e {
            Expression::Call(m, n, _) => (m, n),
            _ => panic!(),
        };
        let t = self.gen_var();
        let call_t = Type::Arrow(Box::new(t.clone()), Box::new(ty.clone()));
        subs = self.judge_type(b, c, d, s, n, t.clone(), subs)?;
        subs = self.judge_type(b, c, d, s, m, call_t.clone(), subs)?;

        m.set_type(call_t);
        n.set_type(t.clone());
        e.set_type(ty);

        Ok(subs)
    }

    fn judge_match(
        &mut self,
        b: Gamma,
        c: Gamma,
        d: Gamma,
        s: GammaStruct,
        e: &mut Expression,
        t: Type,
        mut subs: Theta,
    ) -> Result<Theta, String> {
        let (mat, cases) = match e {
            Expression::Match(m, c, _) => (m, c),
            _ => panic!(),
        };

        let m_type = self.gen_var();
        subs = self.judge_type(b, c, d, s, mat, m_type.clone(), subs)?;

        for (pat, exp) in cases {
            let mut newd = d.clone();
            subs = self.judge_pattern(c, &mut newd, pat, m_type.clone(), subs)?;
            subs = self.judge_type(b, c, &newd, s, exp, t.clone(), subs)?;

            pat.set_type(m_type.clone());
            exp.set_type(t.clone());
        }

        e.set_type(t);

        Ok(subs)
    }

    fn judge_member(
        &mut self,
        b: Gamma,
        c: Gamma,
        d: Gamma,
        structs: GammaStruct,
        e: &mut Expression,
        t: Type,
        mut subs: Theta,
    ) -> Result<Theta, String> {
        let (m, n) = match e {
            Expression::Member(m, n, _) => (m, n),
            _ => unreachable!(),
        };

        let struct_var = self.gen_var();
        subs = self.judge_type(b, c, d, structs, m, struct_var.clone(), subs)?;

        // apply unifier to struct_var to get it's concrete type
        let term = apply_unifier(struct_var.to_term(), &subs);

        let struct_name = match term {
            Term::Const(n) => n,
            Term::Composite(n, _) => n,
            Term::Number(_) | Term::Var(_) => {
                return Err(format!("Type not known for struct"));
            }
        };

        if let Some(members) = structs.get(&struct_name) {
            if let Some(ty) = members.get(n) {
                let ty = self.gen_fresh_type(ty);

                subs = unify(ty.to_term(), t.to_term(), subs)
                    .ok_or(format!("nope not yet i'll write this later"))?;

                m.set_type(struct_var);
                e.set_type(t);

                Ok(subs)
            } else {
                Err(format!(
                    "No member '{}' found for struct '{}'",
                    n, struct_name
                ))
            }
        } else {
            Err(format!("No struct named {} found", struct_name))
        }
    }

    fn judge_multiple(
        &mut self,
        b: Gamma,
        c: Gamma,
        d: Gamma,
        structs: GammaStruct,
        e: &mut Expression,
        t: Type,
        mut subs: Theta,
    ) -> Result<Theta, String> {
        let es = match e {
            Expression::List(a, _) => a,
            _ => panic!(),
        };
        let last_i = es.len() - 1;

        for i in 0..last_i {
            let ty = self.gen_var();
            es[i].set_type(ty.clone());
            subs = self.judge_type(b, c, d, structs, &mut es[i], ty, subs)?;
        }

        let e = &mut es[last_i];
        e.set_type(t.clone());
        self.judge_type(b, c, d, structs, e, t, subs)
    }

    fn judge_type(
        &mut self,
        builtins: Gamma,
        cons: Gamma,
        defs: Gamma,
        structs: GammaStruct,
        e: &mut Expression,
        t: Type,
        subs: Theta,
    ) -> Result<Theta, String> {
        match e {
            Expression::Unit(..) => self.judge_unit(t, subs),
            Expression::Num(..) => self.judge_num(e, t, subs),
            Expression::Identifier(..) => self.judge_var(builtins, cons, defs, e, t, subs),
            Expression::Tuple(..) => self.judge_tuple(builtins, cons, defs, structs, e, t, subs),
            Expression::Lambda1(..) => self.judge_lambda(builtins, cons, defs, structs, e, t, subs),
            Expression::Call(..) => self.judge_call(builtins, cons, defs, structs, e, t, subs),
            Expression::Match(..) => self.judge_match(builtins, cons, defs, structs, e, t, subs),
            Expression::Member(..) => self.judge_member(builtins, cons, defs, structs, e, t, subs),
            Expression::List(..) => self.judge_multiple(builtins, cons, defs, structs, e, t, subs),
        }
    }

    fn judge_pattern_num(
        &mut self,
        e: &mut Pattern,
        t: Type,
        subs: Theta,
    ) -> Result<Theta, String> {
        let tname = apply_unifier(t.to_term(), &subs).name();
        let v = self.gen_num_var();
        e.set_type(v.clone());
        unify(v.to_term(), t.to_term(), subs)
            .ok_or(format!("Type Mismatch: Expected {v:?} found {:?}", tname))
    }

    fn judge_pattern_var(
        &mut self,
        d: Gamma,
        p: &mut Pattern,
        t: Type,
        mut subs: Theta,
    ) -> Result<Theta, String> {
        let x = match p {
            Pattern::Var(x, _) => x,
            _ => panic!(),
        };

        let x = self.apply_gamma(&x, d).unwrap();

        let tname = apply_unifier(t.to_term(), &subs).name();
        let xname = apply_unifier(x.to_term(), &subs).name();

        subs = unify(x.to_term(), t.to_term(), subs).ok_or(format!(
            "Type Mismatch: Expected {:?} found {:?}",
            xname, tname
        ))?;

        p.set_type(t);

        Ok(subs)
    }

    fn judge_pattern_tuple(
        &mut self,
        c: Gamma,
        d: Gamma,
        p: &mut Pattern,
        t: Type,
        mut subs: Theta,
    ) -> Result<Theta, String> {
        let mut ts = vec![];
        let ps = match p {
            Pattern::Tuple(es, _) => es,
            _ => panic!(),
        };

        for pat in ps {
            let ty = self.gen_var();
            ts.push(ty.clone());
            subs = self.judge_pattern_helper(c, d, pat, ty.clone(), subs)?;

            pat.set_type(ty);
        }

        let tname = apply_unifier(t.to_term(), &subs).name();
        let xname = apply_unifier(Type::Tuple(ts.clone()).to_term(), &subs).name();

        subs = unify(Type::Tuple(ts).to_term(), t.to_term(), subs).ok_or(format!(
            "Type Mismatch: Expected {:?} found {:?}",
            xname, tname
        ))?;

        p.set_type(t);

        Ok(subs)
    }

    fn judge_pattern_cons(
        &mut self,
        c: Gamma,
        d: Gamma,
        p: &mut Pattern,
        t: Type,
        mut subs: Theta,
    ) -> Result<Theta, String> {
        let (m, n) = match p {
            Pattern::Cons(m, n, _) => (m, n),
            _ => panic!(),
        };

        let newt = self.gen_var();
        subs = self.judge_type(
            &HashMap::new(),
            c,
            &HashMap::new(),
            &HashMap::new(),
            &mut Expression::Identifier(m.clone(), None),
            Type::Arrow(Box::new(newt.clone()), Box::new(t.clone())),
            subs,
        )?;

        subs = self.judge_pattern_helper(c, d, n, newt.clone(), subs)?;

        n.set_type(newt);
        p.set_type(t);

        Ok(subs)
    }

    fn judge_pattern_helper(
        &mut self,
        c: Gamma,
        d: Gamma,
        p: &mut Pattern,
        t: Type,
        subs: Theta,
    ) -> Result<Theta, String> {
        match p {
            Pattern::Any(..) => Ok(subs),
            Pattern::Namespace(..) => panic!(),
            Pattern::Unit(..) => self.judge_unit(t, subs),
            Pattern::Num(..) => self.judge_pattern_num(p, t, subs),
            Pattern::Var(..) => self.judge_pattern_var(d, p, t, subs),
            Pattern::Tuple(..) => self.judge_pattern_tuple(c, d, p, t, subs),
            Pattern::Cons(..) => self.judge_pattern_cons(c, d, p, t, subs),
        }
    }

    fn judge_pattern(
        &mut self,
        c: Gamma,
        d: MutGamma,
        p: &mut Pattern,
        t: Type,
        subs: Theta,
    ) -> Result<Theta, String> {
        let vars = p.free_vars();

        // check that there are no duplicate vars
        {
            let mut m = HashSet::new();
            for v in vars.iter() {
                m.insert(v);
            }

            if m.len() != vars.len() {
                return Err("Duplicate Variables in pattern".to_string());
            }
        }

        // Add all the vars to dec2 with new type variables
        for v in vars {
            d.insert(v, self.gen_var());
        }

        self.judge_pattern_helper(c, d, p, t, subs)
    }
}
