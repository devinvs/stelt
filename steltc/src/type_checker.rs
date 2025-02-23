use std::collections::HashMap;
use std::collections::HashSet;

use crate::mir::Constraint;
use crate::mir::MIRExpression as Expression;
use crate::parse_tree::{Pattern, Type};
use crate::unify::apply_unifier;
use crate::unify::unify;

use crate::mir::MIRTree;

type Theta = HashMap<Type, Type>;
type Gamma<'a> = &'a HashMap<String, Type>;
type MutGamma<'a> = &'a mut HashMap<String, Type>;

impl Type {
    pub fn map(&self, m: &HashMap<String, Type>) -> Self {
        match self {
            Self::GenVar(s) => m.get(s).unwrap().clone(),
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
    pub fn check_program(
        &mut self,
        tree: &mut MIRTree,
        impl_map: &HashMap<String, Vec<(String, Type)>>,
    ) -> Result<(), String> {
        let mut builtins = HashMap::new();

        // llvm! macro always has the correct output type. Only
        // suitable when the output type is not generic.
        builtins.insert(
            "llvm!".to_string(),
            Type::ForAll(
                vec!["a".to_string()],
                vec![],
                Box::new(Type::Arrow(
                    Box::new(Type::Tuple(vec![Type::Str, Type::Str])),
                    Box::new(Type::GenVar("a".to_string())),
                )),
            ),
        );

        // Check all defs
        for (name, def) in tree.defs.iter_mut() {
            // Don't type check imported functions
            let ty = tree.declarations.get(name).unwrap().clone();
            let subs = self.check_expression(
                &builtins,
                &tree.constructors,
                &tree.declarations,
                def,
                impl_map,
                &tree.private_impl_map,
                ty.clone(),
            )?;
            def.apply(&subs)
        }

        // Check all functions
        for (name, func) in tree.funcs.iter_mut() {
            let ty = tree.declarations.get(name).unwrap().clone();

            self.check_expression(
                &builtins,
                &tree.constructors,
                &tree.declarations,
                func,
                impl_map,
                &tree.private_impl_map,
                ty.clone(),
            )?;
        }

        Ok(())
    }

    // Check an expression against a type, modifying the tree
    // to be fully typed tree. Constraints are bubbled up to
    // here and are checked against the real impls and impls
    // inferred by constraints
    fn check_expression(
        &mut self,
        b: Gamma,
        c: Gamma,
        d: Gamma,
        e: &mut Expression,
        impls: &HashMap<String, Vec<(String, Type)>>,
        private_impls: &HashMap<String, Vec<(String, Type)>>,
        t: Type,
    ) -> Result<Theta, String> {
        let (simple, gen_cons) = match t {
            Type::ForAll(_, cs, t) => (*t, cs),
            _ => (t, vec![]),
        };

        let simple = match simple {
            t => t,
        };

        // Generate subs and constraints for expression, and apply them to the tree
        let (subs, cons) = self.judge_type(b, c, d, e, simple.clone(), HashMap::new())?;
        e.apply(&subs);

        // Check constraints against generic constraints and impls
        // Since all constraints have already been expanded via their
        // typefunctions we just do type unification on the needed type
        // constraint and the provided type constraints from impls and gen_cons
        'outer: for Constraint(tfname, t) in cons {
            // the type of of the constraint we need to fill
            let t = apply_unifier(t, &subs);

            // generic constraints of this expression provide extra implementations,
            // and thus get first priority in checking
            for Constraint(gtfun, gt) in gen_cons.iter() {
                if &tfname == gtfun && unify(gt.clone(), t.clone(), subs.clone()).is_some() {
                    // Found constraint impl in generic constraints
                    continue 'outer;
                }
            }

            let imp = private_impls
                .get(&tfname)
                .unwrap_or_else(|| impls.get(&tfname).expect("tfun not in scope"));

            // next we check the private impls of this type function
            for (_, ty) in imp.iter() {
                let ty = self.gen_fresh_type(ty).0;
                if unify(ty.clone(), t.clone(), subs.clone()).is_some() {
                    continue 'outer;
                }
            }

            // Fail
            return Err(format!("Failed to find {tfname} with type {t:?}"));
        }

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

    fn gen_fresh_type(&mut self, t: &Type) -> (Type, Vec<Constraint>) {
        match t {
            Type::ForAll(vars, cons, inner) => {
                let mut m = HashMap::new();
                for v in vars {
                    m.insert(v.clone(), self.gen_var());
                }

                let cons = cons
                    .into_iter()
                    .map(|Constraint(name, t)| Constraint(name.clone(), t.map(&m)))
                    .collect();

                (inner.map(&m), cons)
            }
            a => (a.clone(), vec![]),
        }
    }

    fn apply_gamma_all(
        &mut self,
        n: &String,
        b: Gamma,
        c: Gamma,
        d: Gamma,
    ) -> Option<(Type, Vec<Constraint>)> {
        match (b.get(n), c.get(n), d.get(n)) {
            (Some(t), _, _) => Some(t),
            (_, Some(t), _) => Some(t),
            (_, _, Some(t)) => Some(t),
            _ => None,
        }
        .map(|t| self.gen_fresh_type(t))
    }

    fn judge_unit(&mut self, t: Type, subs: Theta) -> Result<(Theta, Vec<Constraint>), String> {
        let subs = unify(Type::Unit, t.clone(), subs.clone()).ok_or_else(|| {
            let realtype = apply_unifier(t, &subs);
            format!("Type mismatch: Expected () found {:?}", realtype)
        })?;
        Ok((subs, vec![]))
    }

    fn judge_bool(&self, t: Type, subs: Theta) -> Result<(Theta, Vec<Constraint>), String> {
        let subs = unify(Type::Bool, t.clone(), subs.clone()).ok_or_else(|| {
            let realtype = apply_unifier(t, &subs);
            format!("Type mismatch: Expected bool found {:?}", realtype)
        })?;
        Ok((subs, vec![]))
    }

    fn judge_str(&self, t: Type, subs: Theta) -> Result<(Theta, Vec<Constraint>), String> {
        let subs = unify(Type::Str, t.clone(), subs.clone()).ok_or_else(|| {
            let realtype = apply_unifier(t, &subs);
            format!("Type mismatch: Expected str found {:?}", realtype)
        })?;
        Ok((subs, vec![]))
    }

    fn judge_num(
        &mut self,
        e: &mut Expression,
        t: Type,
        subs: Theta,
    ) -> Result<(Theta, Vec<Constraint>), String> {
        let v = self.gen_num_var();
        e.set_type(v.clone());
        let subs = unify(v.clone(), t.clone(), subs.clone()).ok_or_else(|| {
            let realtype = apply_unifier(t.clone(), &subs);
            format!("Type Mismatch: Expected {v:?} found {:?}", realtype)
        })?;
        Ok((subs, vec![]))
    }

    fn judge_var(
        &mut self,
        builtins: Gamma,
        cons: Gamma,
        defined: Gamma,
        e: &mut Expression,
        t: Type,
        subs: Theta,
    ) -> Result<(Theta, Vec<Constraint>), String> {
        let name = match e {
            Expression::Identifier(a, None) => a,
            _ => panic!(),
        };
        let (x, cons) = self
            .apply_gamma_all(&name, builtins, cons, defined)
            .ok_or(format!(
                "judge_var: Type not known for {name:?}\n{defined:#?}"
            ))?;

        let theta = unify(x.clone(), t.clone(), subs.clone()).ok_or_else(|| {
            let tname = apply_unifier(t.clone(), &subs);
            let xname = apply_unifier(x, &subs);

            format!(
                "Type Mismatch: Expected {:?} found {:?}\n{:?}",
                tname, xname, name,
            )
        })?;

        e.set_type(t);
        Ok((theta, cons))
    }

    fn judge_tuple(
        &mut self,
        b: Gamma,
        c: Gamma,
        d: Gamma,
        e: &mut Expression,
        t: Type,
        mut subs: Theta,
    ) -> Result<(Theta, Vec<Constraint>), String> {
        let mut ts = vec![];
        let mut cons = vec![];

        match e {
            Expression::Tuple(es, _) => {
                for exp in es {
                    let tv = self.gen_var();
                    let (sbs, ncons) = self.judge_type(b, c, d, exp, tv.clone(), subs)?;
                    subs = sbs;
                    cons.extend(ncons);
                    ts.push(tv);
                }
            }
            _ => panic!(),
        }

        let subs = unify(Type::Tuple(ts.clone()), t.clone(), subs.clone()).ok_or_else(|| {
            let tname = apply_unifier(t.clone(), &subs);
            let xname = apply_unifier(Type::Tuple(ts.clone()), &subs);
            format!("Type Mismatch: Expected {:?} found {:?}", xname, tname)
        })?;

        e.set_type(t);

        Ok((subs, cons))
    }

    fn judge_list(
        &mut self,
        b: Gamma,
        c: Gamma,
        d: Gamma,
        e: &mut Expression,
        t: Type,
        mut subs: Theta,
    ) -> Result<(Theta, Vec<Constraint>), String> {
        let mut ts = vec![];
        let mut cons = vec![];

        match e {
            Expression::List(es, _) => {
                for exp in es {
                    let tv = self.gen_var();
                    let (sbs, ncons) = self.judge_type(b, c, d, exp, tv.clone(), subs)?;
                    subs = sbs;
                    cons.extend(ncons);
                    ts.push(tv);
                }
            }
            _ => panic!(),
        }

        let tout = ts.last().unwrap().clone();

        let subs = unify(tout.clone(), t.clone(), subs.clone()).ok_or_else(|| {
            let tname = apply_unifier(t.clone(), &subs);
            let xname = apply_unifier(tout, &subs);
            format!("Type Mismatch: Expected {:?} found {:?}", xname, tname)
        })?;

        e.set_type(t);

        Ok((subs, cons))
    }

    fn judge_lambda(
        &mut self,
        b: Gamma,
        c: Gamma,
        d: Gamma,
        e: &mut Expression,
        ty: Type,
        mut subs: Theta,
    ) -> Result<(Theta, Vec<Constraint>), String> {
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

        let (sbs, cons) = self.judge_type(b, c, &d, m, t2.clone(), subs)?;
        subs = sbs;

        subs = unify(
            Type::Arrow(Box::new(t1.clone()), Box::new(t2.clone())),
            ty.clone(),
            subs.clone(),
        )
        .ok_or_else(|| {
            let tname = apply_unifier(ty.clone(), &subs);
            let xname = apply_unifier(
                Type::Arrow(Box::new(t1.clone()), Box::new(t2.clone())),
                &subs,
            );

            format!(
                "judge_lambda: Type Mismatch: Expected {:?} found {:?}",
                tname, xname
            )
        })?;

        m.set_type(t2.clone());
        e.set_type(ty.clone());

        Ok((subs, cons))
    }

    fn judge_call(
        &mut self,
        b: Gamma,
        c: Gamma,
        d: Gamma,
        e: &mut Expression,
        ty: Type,
        subs: Theta,
    ) -> Result<(Theta, Vec<Constraint>), String> {
        let (m, n) = match e {
            Expression::Call(m, n, _) => (m, n),
            _ => panic!(),
        };
        let t = self.gen_var();
        let call_t = Type::Arrow(Box::new(t.clone()), Box::new(ty.clone()));
        let mut cons = vec![];

        let (sbs, a) = self.judge_type(b, c, d, n, t.clone(), subs)?;
        let (sbs2, b) = self.judge_type(b, c, d, m, call_t.clone(), sbs)?;

        cons.extend(a);
        cons.extend(b);

        m.set_type(call_t);
        n.set_type(t.clone());
        e.set_type(ty);

        Ok((sbs2, cons))
    }

    fn judge_match(
        &mut self,
        b: Gamma,
        c: Gamma,
        d: Gamma,
        e: &mut Expression,
        t: Type,
        mut subs: Theta,
    ) -> Result<(Theta, Vec<Constraint>), String> {
        let (mat, cases) = match e {
            Expression::Match(m, c, _) => (m, c),
            _ => panic!(),
        };

        let mut cons = vec![];

        let m_type = self.gen_var();
        let (subs1, mut ncons) = self.judge_type(b, c, d, mat, m_type.clone(), subs)?;
        subs = subs1;

        cons.extend(ncons);

        for (pat, exp) in cases {
            let mut newd = d.clone();
            (subs, ncons) = self.judge_pattern(c, &mut newd, pat, m_type.clone(), subs)?;
            cons.extend(ncons);
            (subs, ncons) = self.judge_type(b, c, &newd, exp, t.clone(), subs)?;
            cons.extend(ncons);

            pat.set_type(m_type.clone());
            exp.set_type(t.clone());
        }

        e.set_type(t);

        Ok((subs, cons))
    }

    fn judge_type(
        &mut self,
        builtins: Gamma,
        cons: Gamma,
        defs: Gamma,
        e: &mut Expression,
        t: Type,
        subs: Theta,
    ) -> Result<(Theta, Vec<Constraint>), String> {
        match e {
            Expression::Unit(..) => self.judge_unit(t, subs),
            Expression::True | Expression::False => self.judge_bool(t, subs),
            Expression::String(..) => self.judge_str(t, subs),
            Expression::Num(..) => self.judge_num(e, t, subs),
            Expression::Identifier(..) => self.judge_var(builtins, cons, defs, e, t, subs),
            Expression::Tuple(..) => self.judge_tuple(builtins, cons, defs, e, t, subs),
            Expression::List(..) => self.judge_list(builtins, cons, defs, e, t, subs),
            Expression::Lambda1(..) => self.judge_lambda(builtins, cons, defs, e, t, subs),
            Expression::Call(..) => self.judge_call(builtins, cons, defs, e, t, subs),
            Expression::Match(..) => self.judge_match(builtins, cons, defs, e, t, subs),
        }
    }

    fn judge_pattern_num(
        &mut self,
        e: &mut Pattern,
        t: Type,
        subs: Theta,
    ) -> Result<(Theta, Vec<Constraint>), String> {
        let v = self.gen_num_var();
        e.set_type(v.clone());
        let subs = unify(v.clone(), t.clone(), subs.clone()).ok_or_else(|| {
            let tname = apply_unifier(t, &subs);
            format!("Type Mismatch: Expected {v:?} found {:?}", tname)
        })?;

        Ok((subs, vec![]))
    }

    fn judge_pattern_str(
        &mut self,
        t: Type,
        subs: Theta,
    ) -> Result<(Theta, Vec<Constraint>), String> {
        let subs = unify(Type::Str, t.clone(), subs.clone()).ok_or_else(|| {
            let tname = apply_unifier(t, &subs);
            format!("Type Mismatch: Expected str found {:?}", tname)
        })?;

        Ok((subs, vec![]))
    }

    fn judge_pattern_var(
        &mut self,
        d: Gamma,
        p: &mut Pattern,
        t: Type,
        mut subs: Theta,
    ) -> Result<(Theta, Vec<Constraint>), String> {
        let x = match p {
            Pattern::Var(x, _) => x,
            _ => panic!(),
        };

        let (x, cons) = self
            .apply_gamma_all(&x, &HashMap::new(), &HashMap::new(), d)
            .unwrap();

        subs = unify(x.clone(), t.clone(), subs.clone()).ok_or_else(|| {
            let tname = apply_unifier(t.clone(), &subs);
            let xname = apply_unifier(x, &subs);

            format!("Type Mismatch: Expected {:?} found {:?}", xname, tname)
        })?;

        p.set_type(t);

        Ok((subs, cons))
    }

    fn judge_pattern_tuple(
        &mut self,
        c: Gamma,
        d: Gamma,
        p: &mut Pattern,
        t: Type,
        mut subs: Theta,
    ) -> Result<(Theta, Vec<Constraint>), String> {
        let mut ts = vec![];
        let ps = match p {
            Pattern::Tuple(es, _) => es,
            _ => panic!(),
        };

        let mut cons = vec![];

        for pat in ps {
            let ty = self.gen_var();
            ts.push(ty.clone());
            let (sbs1, ncons) = self.judge_pattern_helper(c, d, pat, ty.clone(), subs)?;
            subs = sbs1;
            cons.extend(ncons);

            pat.set_type(ty);
        }

        subs = unify(Type::Tuple(ts.clone()), t.clone(), subs.clone()).ok_or_else(|| {
            let tname = apply_unifier(t.clone(), &subs);
            let xname = apply_unifier(Type::Tuple(ts.clone()), &subs);

            format!("Type Mismatch: Expected {:?} found {:?}", xname, tname)
        })?;

        p.set_type(t);

        Ok((subs, cons))
    }

    fn judge_pattern_cons(
        &mut self,
        c: Gamma,
        d: Gamma,
        p: &mut Pattern,
        t: Type,
        mut subs: Theta,
    ) -> Result<(Theta, Vec<Constraint>), String> {
        let (m, n) = match p {
            Pattern::Cons(m, n, _) => (m, n),
            _ => panic!(),
        };
        let newt = self.gen_var();
        let (sbs, mut cons) = self.judge_type(
            &HashMap::new(),
            c,
            &HashMap::new(),
            &mut Expression::Identifier(m.clone(), None),
            Type::Arrow(Box::new(newt.clone()), Box::new(t.clone())),
            subs,
        )?;
        subs = sbs;

        let (sbs, ncons) = self.judge_pattern_helper(c, d, n, newt.clone(), subs)?;
        subs = sbs;
        cons.extend(ncons);

        n.set_type(newt);
        p.set_type(t);

        Ok((subs, cons))
    }

    fn judge_pattern_helper(
        &mut self,
        c: Gamma,
        d: Gamma,
        p: &mut Pattern,
        t: Type,
        subs: Theta,
    ) -> Result<(Theta, Vec<Constraint>), String> {
        match p {
            Pattern::Any(..) => Ok((subs, vec![])),
            Pattern::True | Pattern::False => self.judge_bool(t, subs),
            Pattern::Unit(..) => self.judge_unit(t, subs),
            Pattern::String(..) => self.judge_pattern_str(t, subs),
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
    ) -> Result<(Theta, Vec<Constraint>), String> {
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
