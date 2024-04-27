use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;

use crate::parse_tree::{DataDecl, Expression, ParseTree, Pattern, QualType, Type, TypeCons, Vis};
use crate::resolve::Module;

use crate::unify::apply_unifier;
use crate::unify::unify;

use crate::parse_tree;

type Theta = HashMap<Type, Type>;

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Constraint(pub String, pub Type);

// Transform a parse tree constraint to a mir constraint
// using the typefunction as a template
pub fn trans_cons(
    cons: parse_tree::Constraint,
    typefns: &HashMap<String, (Vis, parse_tree::TypeFun)>,
) -> Constraint {
    let parse_tree::Constraint(name, ts) = cons;
    let (_, tf) = &typefns[&name];

    // Create substitutions for this constraint
    let mut subs = HashMap::new();
    for (var, arg) in tf.vars.iter().zip(ts.iter()) {
        subs.insert(var.clone(), arg.clone());
    }

    // The real type of the expanded constraint
    let real_type = tf.ty.clone().replace_all(&subs);
    Constraint(name, real_type)
}

pub fn typefn_type(tf: parse_tree::TypeFun) -> Type {
    // Need to sub each tf.var for genvar
    let mut subs = HashMap::new();
    for var in tf.vars.clone() {
        subs.insert(var.clone(), Type::GenVar(var));
    }

    let t = tf.ty.replace_all(&subs);
    let cons = vec![Constraint(tf.name.clone(), t.clone())];

    Type::ForAll(tf.vars, cons, Box::new(t))
}

#[derive(Debug)]
pub struct MIRTree {
    pub external: HashSet<String>,
    pub types: Vec<(String, (Vis, DataDecl))>,
    pub typedecls: HashMap<String, (Vis, Type)>,
    pub funcs: HashMap<String, MIRExpression>,
    pub defs: HashMap<String, MIRExpression>,
    pub private_impl_map: HashMap<String, Vec<(String, Type)>>,

    pub constructors: HashMap<String, Type>,
    pub declarations: HashMap<String, Type>,
}

impl MIRTree {
    pub fn from(tree: ParseTree, modules: &HashMap<String, Module>) -> Self {
        // First things first: get the generic args out of the types
        // and convert to forall types
        //
        // This includes all typedecls, typefns, and impls
        let mut typedecls = HashMap::new();

        let type_names = tree
            .types
            .iter()
            .map(|dd| dd.0.clone())
            .collect::<HashSet<_>>();

        let mut typefuns = tree.typefuns.clone();

        for module in modules.values() {
            for (name, tf) in module.pub_typefn.iter() {
                typefuns.insert(name.clone(), (Vis::Public, tf.clone()));
            }
        }

        // Typedecls get their generics extracted into a forall type along with
        // the constraints from the QualType
        for (name, (vis, QualType(cons, t))) in tree.typedecls.into_iter() {
            let cons = cons.into_iter().map(|c| trans_cons(c, &typefuns)).collect();
            let t = t.extract_vars(&type_names, cons);
            typedecls.insert(name, (vis, t));
        }

        let mut declarations = HashMap::new();

        // Type functions can have generic variables but not generic constraints
        // Type functions type check as a forall type and provide themselves as their constraint
        for (name, (_, typefn)) in tree.typefuns.clone() {
            let t = typefn_type(typefn);
            declarations.insert(name, t);
        }

        // Add all user defined type definitions to declarations
        for (name, (_, t)) in typedecls.iter() {
            declarations.insert(name.clone(), t.clone());
        }

        // Add all type constructors to conss
        let mut constructors = HashMap::new();

        for (name, (_, decl)) in tree.types.iter() {
            match decl {
                DataDecl(_, args, cons) => {
                    for cons in cons {
                        let outt = if args.len() == 0 {
                            Box::new(Type::Ident(name.clone()))
                        } else {
                            Box::new(Type::Generic(
                                args.clone().into_iter().map(|s| Type::GenVar(s)).collect(),
                                Box::new(Type::Ident(name.clone())),
                            ))
                        };

                        let mut cons = cons.clone();

                        for a in args.clone() {
                            cons.args = cons.args.replace(&a, &Type::GenVar(a.clone()));
                        }

                        constructors.insert(
                            cons.name.clone(),
                            Type::ForAll(
                                args.clone(),
                                vec![],
                                Box::new(Type::Arrow(Box::new(cons.args.clone()), outt)),
                            ),
                        );
                    }
                }
            }
        }

        let mut idents = HashSet::new();
        idents.extend(constructors.clone().into_keys());
        idents.extend(declarations.clone().into_keys());

        let mut defs = HashMap::new();

        // Transform each definition into it's intermediate representation
        tree.defs.into_iter().for_each(|(name, def)| {
            defs.insert(name, MIRExpression::from(def, &constructors));
        });

        // Convert each list of function definitions into a lambda match expression
        let mut funcs = HashMap::new();
        tree.funcs.into_iter().for_each(|(name, defs)| {
            let v = crate::gen_var("in");

            funcs.insert(
                name,
                MIRExpression::Lambda1(
                    Some(v.clone()),
                    Box::new(MIRExpression::Match(
                        Box::new(MIRExpression::Identifier(v, None)),
                        defs.into_iter()
                            .map(|def| {
                                (
                                    def.args.trans_cons(&constructors),
                                    MIRExpression::from(def.body, &constructors),
                                )
                            })
                            .collect(),
                        None,
                    )),
                    None,
                ),
            );
        });

        Self {
            external: tree.external,
            types: tree.types.into_iter().collect(),
            typedecls,
            funcs,
            defs,
            constructors,
            declarations,
            private_impl_map: tree.private_impl_map,
        }
    }

    pub fn with_concrete_types(
        mut self,
        impl_map: &HashMap<String, Vec<(String, Type)>>,
        modules: &HashMap<String, Module>,
    ) -> Self {
        let mut generic_decls = HashMap::new();
        let mut concrete_decls = HashMap::new();

        // split out generic typedecls from the concrete ones
        for (name, (vis, t)) in self.typedecls {
            match t {
                Type::ForAll(args, cons, inner) => {
                    if args.len() == 0 {
                        concrete_decls.insert(name, (vis, *inner));
                    } else {
                        generic_decls.insert(name, Type::ForAll(args, cons, inner));
                    }
                }
                a => {
                    concrete_decls.insert(name, (vis, a));
                }
            }
        }

        let mut concrete_funcs = HashMap::new();

        let cons = self
            .types
            .iter()
            .filter_map(|(_, (_, t))| match &t {
                DataDecl(_, _, cons) => {
                    Some(cons.iter().map(|tc| tc.name.clone()).collect::<Vec<_>>())
                }
            })
            .flatten()
            .collect();

        let mut concrete_queue = VecDeque::new();
        concrete_queue.extend(concrete_decls.clone().into_iter().filter_map(|(name, _)| {
            let body = self.funcs.get(&name)?.clone();
            Some((name.clone(), body))
        }));

        let mut generic_types = HashMap::new();
        let mut concrete_types = HashMap::new();

        while let Some((name, body)) = concrete_queue.pop_front() {
            // resolve the typefn to their implementation
            let (body, imported) = body.resolve_typefn(impl_map);

            for import in imported {
                let (tf, _) = import.rsplit_once("$").unwrap();

                let imp = impl_map[tf]
                    .iter()
                    .find(|(n, _)| *n == import)
                    .unwrap()
                    .1
                    .clone();

                concrete_decls.insert(import, (Vis::Import, imp));
            }

            // extract generic calls, getting a new body and a list of those calls
            let (f, calls) = body.extract_calls(&generic_decls, &cons);
            // insert into our concrete functions
            concrete_funcs.insert(name.clone(), f);

            // each of our generic calls is a tuple of (n n' t) where
            // - n is the name of the generic function
            // - n' is the name of the concrete version of the generic function
            // - t is the type of the concrete function
            //
            // so for each call we check for t' in our concrete_funcs
            // if it does not exist we add t' and the concrete body
            // to the concrete queue so as to extract any typefn/other generic calls
            for (n, n_prime, t) in calls {
                if !concrete_funcs.contains_key(&n_prime) {
                    // add to concrete_decls ig, ughh
                    concrete_decls.insert(n_prime.clone(), (Vis::Private, t.clone()));

                    eprintln!("w {n}");
                    let oldty = generic_decls[&n].clone();
                    let subs = oldty.get_generic_subs(&t);

                    let body = self.funcs[&n].clone().sub_types(&subs);
                    concrete_queue.push_back((n_prime, body));
                }
            }
        }

        //
        // Get a list of all the types that we have access to
        //
        let mut types = vec![];

        // First add all our private types
        for (name, (vis, t)) in self.types {
            if vis != Vis::Private {
                continue;
            }

            types.push((name, (vis, t)));
        }

        // Then add all public types from all modules
        // this is necessary since generics could inevitably
        // use a type that we haven't imported
        for module in modules.values() {
            for (name, data) in module.pub_data.iter() {
                types.push((name.clone(), (Vis::Public, data.clone())));
            }
        }

        //
        // split out the generic type prototypes and the concrete types
        //
        for (name, (vis, t)) in types {
            let argc = match t.clone() {
                DataDecl(_, args, _) => args.len(),
            };

            if argc == 0 {
                concrete_types.insert(name, (vis, t));
            } else {
                generic_types.insert(name, t);
            }
        }

        // For each typedecl replace generics with concrete instances
        for (_, (_, t)) in concrete_decls.iter_mut() {
            let (newt, concs) = t.clone().extract_generics(&generic_types);
            for conc in concs {
                concrete_types.insert(conc.name(), (Vis::Private, conc));
            }
            *t = newt;
        }

        // finally, for every concrete type extract the generics from their members and constructors
        let mut other_concretes = HashMap::new();
        for (_, (_, t)) in concrete_types.iter_mut() {
            *t = match t {
                DataDecl(n, v, cons) => {
                    let cons = cons
                        .into_iter()
                        .map(|TypeCons { name, args }| {
                            let (newt, concs) = args.clone().extract_generics(&generic_types);
                            for conc in concs {
                                other_concretes.insert(conc.name(), (Vis::Private, conc));
                            }
                            TypeCons {
                                name: name.clone(),
                                args: newt,
                            }
                        })
                        .collect();

                    DataDecl(n.clone(), v.clone(), cons)
                }
            };
        }

        concrete_types.extend(other_concretes);

        // change type constructor names to have their type as a prefix

        // for (_, (_, data)) in concrete_types.iter_mut() {
        //     let name = data.name();
        //     match data {
        //         DataDecl(_, _, cons) => {
        //             for cons in cons.iter_mut() {
        //                 let newname = format!("{}${}$", cons.name, name);
        //                 cons.name = newname;
        //             }
        //         }
        //     }
        // }

        self.types = concrete_types.into_iter().collect();
        self.typedecls = concrete_decls;
        self.funcs = concrete_funcs;

        // remove recursion from recursive types with boxing
        let data = self.types.clone();
        for (name, (_, d)) in data.into_iter() {
            let d = d.remove_recursion(&name, &mut self.types);
            *self
                .types
                .iter_mut()
                .find(|(n, _)| *n == name)
                .map(|(_, (_, a))| a)
                .unwrap() = d;
        }

        self
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum MIRExpression {
    /// An identifier that we can evaluate.
    /// usually a variable that was defined previously
    Identifier(String, Option<Type>),

    /// A tuple of expressions
    Tuple(Vec<MIRExpression>, Option<Type>),

    /// Test a list of patterns against an expression, returning the expression that matches
    Match(
        Box<MIRExpression>,
        Vec<(Pattern, MIRExpression)>,
        Option<Type>,
    ),

    /// Call the function with args
    /// Can be a global function, a lambda, or a constructor
    Call(Box<MIRExpression>, Box<MIRExpression>, Option<Type>),

    /// A lambda expression with pattern args and an expression body
    Lambda1(Option<String>, Box<MIRExpression>, Option<Type>),

    // Constant Fields
    Num(u64, Option<Type>), // A Number Literal
    Unit(Option<Type>),
    True,
    False,
}

impl MIRExpression {
    fn sub_types(self, subs: &HashMap<String, Type>) -> Self {
        let t = self.ty().replace_all(subs);

        match self {
            MIRExpression::True => MIRExpression::True,
            MIRExpression::False => MIRExpression::False,
            MIRExpression::Identifier(n, _) => MIRExpression::Identifier(n, Some(t)),
            MIRExpression::Unit(_) => MIRExpression::Unit(Some(t)),
            MIRExpression::Num(n, _) => MIRExpression::Num(n, Some(t)),
            MIRExpression::Call(m, n, _) => MIRExpression::Call(
                Box::new(m.sub_types(subs)),
                Box::new(n.sub_types(subs)),
                Some(t),
            ),
            MIRExpression::Lambda1(x, m, _) => {
                MIRExpression::Lambda1(x, Box::new(m.sub_types(subs)), Some(t))
            }
            MIRExpression::Match(m, ps, _) => MIRExpression::Match(
                Box::new(m.sub_types(subs)),
                ps.into_iter()
                    .map(|(p, e)| (p.sub_types(subs), e.sub_types(subs)))
                    .collect(),
                Some(t),
            ),
            MIRExpression::Tuple(es, _) => {
                MIRExpression::Tuple(es.into_iter().map(|e| e.sub_types(subs)).collect(), Some(t))
            }
        }
    }

    fn from(tree: Expression, cons: &HashMap<String, Type>) -> Self {
        match tree {
            Expression::List(..) => todo!(),
            Expression::True => Self::True,
            Expression::False => Self::False,
            Expression::Num(n) => Self::Num(n, None),
            Expression::Unit => Self::Unit(Some(Type::Unit)),
            Expression::Identifier(i) => Self::Identifier(i, None),
            Expression::Tuple(es) => Self::Tuple(
                es.into_iter()
                    .map(|e| MIRExpression::from(e, cons))
                    .collect(),
                None,
            ),
            Expression::Match(m, cases) => Self::Match(
                Box::new(MIRExpression::from(*m, cons)),
                cases
                    .into_iter()
                    .map(|(p, e)| (p.trans_cons(cons), MIRExpression::from(e, cons)))
                    .collect(),
                None,
            ),
            Expression::Call(f, args) => Self::Call(
                Box::new(MIRExpression::from(*f, cons)),
                Box::new(MIRExpression::from(*args, cons)),
                None,
            ),
            Expression::Lambda(pat, body) => match pat.trans_cons(cons) {
                Pattern::Var(s, _) => {
                    Self::Lambda1(Some(s), Box::new(MIRExpression::from(*body, cons)), None)
                }
                Pattern::Unit(..) => {
                    Self::Lambda1(None, Box::new(MIRExpression::from(*body, cons)), None)
                }
                p => {
                    let v = crate::gen_var("cons_pat");
                    Self::Lambda1(
                        Some(v.clone()),
                        Box::new(Self::Match(
                            Box::new(Self::Identifier(v, None)),
                            vec![(p, Self::from(*body, cons))],
                            None,
                        )),
                        None,
                    )
                }
            },
            Expression::Let(pat, val, body) => Self::Match(
                Box::new(MIRExpression::from(*val, cons)),
                vec![(pat.trans_cons(cons), MIRExpression::from(*body, cons))],
                None,
            ),
            Expression::If(cond, then, els) => Self::Match(
                Box::new(MIRExpression::from(*cond, cons)),
                vec![
                    (Pattern::True, MIRExpression::from(*then, cons)),
                    (Pattern::False, MIRExpression::from(*els, cons)),
                ],
                None,
            ),
        }
    }

    fn resolve_typefn(
        self,
        impl_map: &HashMap<String, Vec<(String, Type)>>,
    ) -> (Self, Vec<String>) {
        match self {
            Self::Identifier(s, Some(t)) => {
                if let Some(impls) = impl_map.get(&s) {
                    let id = resolve_typefn(impls, t.clone()).expect(&format!(
                        "Could not find impl for typefn: {s} of type {t:?}"
                    ));

                    (Self::Identifier(id.clone(), Some(t)), vec![id])
                } else {
                    (Self::Identifier(s, Some(t)), vec![])
                }
            }
            Self::Tuple(exprs, t) => {
                let mut ids = vec![];

                let t = Self::Tuple(
                    exprs
                        .into_iter()
                        .map(|e| {
                            let (a, is) = e.resolve_typefn(impl_map);
                            ids.extend(is);
                            a
                        })
                        .collect(),
                    t,
                );

                (t, ids)
            }
            Self::Match(x, pats, t) => {
                let mut ids = vec![];

                let (x, is) = x.resolve_typefn(impl_map);
                ids.extend(is);

                let m = Self::Match(
                    Box::new(x),
                    pats.into_iter()
                        .map(|(p, e)| {
                            let (e, is) = e.resolve_typefn(impl_map);
                            ids.extend(is);
                            (p, e)
                        })
                        .collect(),
                    t,
                );

                (m, ids)
            }
            Self::Call(m, n, t) => {
                let mut ids = vec![];

                let (m, is) = m.resolve_typefn(impl_map);
                let (n, iss) = n.resolve_typefn(impl_map);

                ids.extend(is);
                ids.extend(iss);

                (Self::Call(Box::new(m), Box::new(n), t), ids)
            }
            Self::Lambda1(x, m, t) => {
                let (m, ids) = m.resolve_typefn(impl_map);
                (Self::Lambda1(x, Box::new(m), t), ids)
            }
            a => (a, vec![]),
        }
    }

    pub fn ty(&self) -> Type {
        match self {
            Self::True => &Some(Type::Bool),
            Self::False => &Some(Type::Bool),
            Self::Identifier(_, t) => t,
            Self::Num(_, t) => t,
            Self::Unit(t) => t,
            Self::Tuple(_, t) => t,
            Self::Match(_, _, t) => t,
            Self::Call(_, _, t) => t,
            Self::Lambda1(_, _, t) => t,
        }
        .clone()
        .expect(&format!("{:?}", self))
    }

    pub fn set_type(&mut self, ty: Type) {
        match self {
            Self::True => {}
            Self::False => {}
            Self::Identifier(_, t) => *t = Some(ty),
            Self::Num(_, t) => *t = Some(ty),
            Self::Unit(t) => *t = Some(ty),
            Self::Tuple(_, t) => *t = Some(ty),
            Self::Match(_, _, t) => *t = Some(ty),
            Self::Call(_, _, t) => *t = Some(ty),
            Self::Lambda1(_, _, t) => *t = Some(ty),
        }
    }

    pub fn apply(&mut self, subs: &Theta) {
        self.set_type(apply_unifier(self.ty(), subs));

        match self {
            Self::Tuple(a, _) => a.iter_mut().for_each(|e| e.apply(subs)),
            Self::Match(a, b, _) => {
                a.apply(subs);

                for (pat, e) in b {
                    pat.apply(subs);
                    e.apply(subs);
                }
            }
            Self::Call(a, b, ..) => {
                a.apply(subs);
                b.apply(subs);
            }
            Self::Lambda1(_, b, ..) => {
                b.apply(subs);
            }
            _ => {}
        }
    }

    fn extract_calls(
        self,
        generics: &HashMap<String, Type>,
        cons: &HashSet<String>,
    ) -> (Self, Vec<(String, String, Type)>) {
        match self {
            MIRExpression::Identifier(name, t) => {
                if generics.contains_key(&name) {
                    let newname = format!("{name}${}$", t.as_ref().unwrap().to_string());

                    (
                        MIRExpression::Identifier(newname.clone(), t.clone()),
                        vec![(name, newname, t.unwrap())],
                    )
                } else if cons.contains(&name) {
                    let out_t = match t.clone().unwrap() {
                        Type::Arrow(_, t) => t,
                        _ => panic!(),
                    };
                    let local_name = name.rsplit_once(".").unwrap().1;

                    let newname = format!("{}.{}", out_t.as_ref().to_string(), local_name);
                    (
                        MIRExpression::Identifier(newname.clone(), t.clone()),
                        vec![],
                    )
                } else {
                    (MIRExpression::Identifier(name, t), vec![])
                }
            }
            MIRExpression::Tuple(es, t) => {
                let mut v = vec![];
                let mut newes = vec![];

                for e in es {
                    let (e, gens) = e.extract_calls(generics, cons);
                    newes.push(e);
                    v.extend(gens);
                }

                (MIRExpression::Tuple(newes, t), v)
            }
            MIRExpression::Call(f, args, t) => {
                let (f, mut gens) = f.extract_calls(generics, cons);
                let (args, gens2) = args.extract_calls(generics, cons);
                gens.extend(gens2);

                (MIRExpression::Call(Box::new(f), Box::new(args), t), gens)
            }
            MIRExpression::Lambda1(arg, body, t) => {
                let (body, gens) = body.extract_calls(generics, cons);
                (MIRExpression::Lambda1(arg, Box::new(body), t), gens)
            }
            MIRExpression::Match(e, ps, t) => {
                // I don't think that we need to check the patterns, but I'm not entirely sure
                // ignore the above comment, that was written by an idiot, we definitely need the patterns

                let (e, mut gens) = e.extract_calls(generics, cons);

                let mut new_ps = vec![];
                for (p, e) in ps {
                    let (e, gens2) = e.extract_calls(generics, cons);
                    let p = p.extract_generics();
                    gens.extend(gens2);
                    new_ps.push((p, e));
                }

                (MIRExpression::Match(Box::new(e), new_ps, t), gens)
            }
            a => (a, vec![]),
        }
    }
}

impl Pattern {
    fn extract_generics(self) -> Self {
        match self {
            Self::Cons(name, args, t) => {
                let local_name = name.rsplit_once(".").unwrap().1;
                let newname = format!("{}.{local_name}", t.as_ref().unwrap().to_string());

                let args = args.extract_generics();

                Self::Cons(newname, Box::new(args), t)
            }
            Self::Tuple(ps, t) => {
                Self::Tuple(ps.into_iter().map(|p| p.extract_generics()).collect(), t)
            }
            a => a,
        }
    }

    fn sub_types(self, subs: &HashMap<String, Type>) -> Self {
        let t = self.ty().replace_all(subs);
        match self {
            Pattern::True => Pattern::True,
            Pattern::False => Pattern::False,
            Pattern::Any(..) => Pattern::Any(Some(t)),
            Pattern::Var(x, _) => Pattern::Var(x, Some(t)),
            Pattern::Unit(_) => Pattern::Unit(Some(t)),
            Pattern::Num(n, _) => Pattern::Num(n, Some(t)),
            Pattern::Tuple(ps, _) => {
                Pattern::Tuple(ps.into_iter().map(|p| p.sub_types(subs)).collect(), Some(t))
            }
            Pattern::Cons(n, args, _) => Pattern::Cons(n, Box::new(args.sub_types(subs)), Some(t)),
        }
    }

    fn trans_cons(self, cons: &HashMap<String, Type>) -> Self {
        match self {
            Self::Var(x, t) => {
                if cons.contains_key(&x) {
                    Self::Cons(x, Box::new(Self::Unit(Some(Type::Unit))), t)
                } else {
                    Self::Var(x, t)
                }
            }
            a => a,
        }
    }

    fn apply(&mut self, subs: &Theta) {
        self.set_type(apply_unifier(self.ty(), subs));

        match self {
            Pattern::Cons(_, a, _) => {
                a.apply(subs);
            }
            Pattern::Tuple(a, _) => a.iter_mut().for_each(|e| e.apply(subs)),
            _ => {}
        }
    }
}

impl Type {
    fn extract_vars(self, types: &HashSet<String>, cons: Vec<Constraint>) -> Type {
        let vars = self.type_vars(types);

        match self {
            Type::ForAll(mut vs, _, t) => {
                vs.extend(vars);
                Type::ForAll(vs, cons, t)
            }
            a => Type::ForAll(vars.into_iter().collect(), cons, Box::new(a)),
        }
    }

    fn type_vars(&self, types: &HashSet<String>) -> HashSet<String> {
        let mut vars = HashSet::new();
        match self {
            Type::ForAll(vs, _, t) => {
                let mut ntypes = types.clone();
                ntypes.extend(vs.clone());

                vars.extend(t.type_vars(&ntypes));
            }
            Type::Generic(ass, b) => {
                for a in ass {
                    vars.extend(a.type_vars(types));
                }

                vars.extend(b.type_vars(types));
            }
            Type::Arrow(a, b) => {
                vars.extend(a.type_vars(types));
                vars.extend(b.type_vars(types));
            }
            Type::Tuple(ass) => {
                for a in ass {
                    vars.extend(a.type_vars(types));
                }
            }
            Type::GenVar(s) => {
                vars.insert(s.clone());
            }
            _ => {}
        }

        vars
    }

    fn fresh(self) -> Self {
        let mut i = 0;

        match self {
            Type::ForAll(vars, _, inner) => {
                let mut m = HashMap::new();
                for v in vars {
                    m.insert(v.clone(), Type::Var(i));
                    i += 1
                }

                inner.map(&m)
            }
            a => a,
        }
    }

    fn get_generic_subs(&self, other: &Type) -> HashMap<String, Type> {
        if let Type::ForAll(vars, _, t) = self {
            let mut name_to_id = HashMap::new();

            // substitute for actual var types
            let mut me = *t.clone();
            for (i, var) in vars.iter().enumerate() {
                name_to_id.insert(var.clone(), i);
                me = me.replace(var, &Type::Var(i));
            }

            let var_to_ty = me.get_var_subs(other);

            name_to_id
                .into_iter()
                .map(|(a, b)| (a, var_to_ty[&b].clone()))
                .collect()
        } else {
            HashMap::new()
        }
    }

    fn get_var_subs(&self, other: &Type) -> HashMap<usize, Type> {
        if self == other {
            return HashMap::new();
        }

        match (self, other) {
            (Type::Var(i), t) => {
                let mut m = HashMap::new();
                m.insert(*i, t.clone());
                m
            }
            (Type::Arrow(from, to), Type::Arrow(from2, to2)) => {
                let mut subs = from.get_var_subs(from2);
                subs.extend(to.get_var_subs(to2));

                subs
            }
            (Type::Generic(vars, t), Type::Generic(vars2, t2)) => {
                let mut subs = t.get_var_subs(t2);

                for (v1, v2) in vars.iter().zip(vars2.iter()) {
                    subs.extend(v1.get_var_subs(v2));
                }

                subs
            }
            (Type::Tuple(ts), Type::Tuple(ts2)) => {
                let mut subs = HashMap::new();

                for (t1, t2) in ts.iter().zip(ts2.iter()) {
                    subs.extend(t1.get_var_subs(t2));
                }

                subs
            }
            (Type::Box(t), Type::Box(t2)) => t.get_var_subs(t2),
            _ => panic!("{self:?}  {other:?}"),
        }
    }

    fn extract_generics(self, generics: &HashMap<String, DataDecl>) -> (Self, Vec<DataDecl>) {
        match self {
            Type::Generic(vals, ty) => {
                // type must be identifier to generic datadecl
                let name = match *ty {
                    Type::Ident(n) => n,
                    _ => panic!("what?"),
                };
                let gen_ty = &generics[&name];

                let mut concrete = vec![];
                // get concrete versions of type args
                let mut new_vals = vec![];
                for val in vals {
                    let (t, concs) = val.extract_generics(generics);
                    concrete.extend(concs);
                    new_vals.push(t);
                }

                let newname = format!(
                    "{}${}$",
                    name,
                    new_vals
                        .iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(",")
                );

                let newt = gen_ty.substitute(newname.clone(), &new_vals);
                concrete.push(newt.clone());

                (Type::Ident(newname), concrete)
            }
            Type::Arrow(a, b) => {
                let (a, mut ts) = a.extract_generics(generics);
                let (b, newts) = b.extract_generics(generics);

                ts.extend(newts);
                (Type::Arrow(Box::new(a), Box::new(b)), ts)
            }
            Type::ForAll(a, c, b) => {
                let (t, ts) = b.extract_generics(generics);
                (Type::ForAll(a, c, Box::new(t)), ts)
            }
            Type::Tuple(ts) => {
                let mut concs = vec![];
                let mut newts = vec![];

                for t in ts {
                    let (newt, conc) = t.extract_generics(generics);
                    newts.push(newt);
                    concs.extend(conc);
                }

                (Type::Tuple(newts), concs)
            }
            Type::Box(t) => t.extract_generics(generics),
            a => (a, vec![]),
        }
    }

    pub fn replace_all(mut self, subs: &HashMap<String, Type>) -> Self {
        for (s, t) in subs {
            self = self.replace(s, t);
        }

        self
    }

    fn replace(self, from: &str, to: &Type) -> Self {
        match self {
            Type::Ident(s) => {
                if s == from {
                    to.clone()
                } else {
                    Type::Ident(s)
                }
            }
            Type::GenVar(a) => {
                if a == from {
                    to.clone()
                } else {
                    Type::GenVar(a)
                }
            }
            Type::Arrow(a, b) => {
                let a = a.replace(from, to);
                let b = b.replace(from, to);

                Type::Arrow(Box::new(a), Box::new(b))
            }
            Type::ForAll(a, c, b) => Type::ForAll(
                a,
                c.into_iter()
                    .map(|Constraint(name, t)| Constraint(name, t.replace(from, to)))
                    .collect(),
                Box::new(b.replace(from, to)),
            ),
            Type::Generic(a, b) => Type::Generic(
                a.into_iter().map(|a| a.replace(from, to)).collect(),
                Box::new(b.replace(from, to)),
            ),
            Type::Tuple(ts) => Type::Tuple(ts.into_iter().map(|t| t.replace(from, to)).collect()),
            Type::Box(t) => Type::Box(Box::new(t.replace(from, to))),
            a => a,
        }
    }
}

impl DataDecl {
    fn substitute(&self, name: String, vals: &Vec<Type>) -> Self {
        match self {
            DataDecl(_, args, cons) => {
                let mut new_cons = vec![];

                for con in cons {
                    let mut con = con.clone();

                    let local_name = con.name.rsplit_once(".").unwrap().1;
                    con.name = format!("{name}.{local_name}");

                    for (arg, val) in args.iter().zip(vals.iter()) {
                        con = con.replace(arg, val);
                    }

                    new_cons.push(con);
                }

                DataDecl(name, vec![], new_cons)
            }
        }
    }

    fn name(&self) -> String {
        match self {
            Self(n, _, _) => n,
        }
        .clone()
    }
}

impl TypeCons {
    fn replace(&self, from: &str, to: &Type) -> Self {
        TypeCons {
            name: self.name.clone(),
            args: self.args.clone().replace(from, to),
        }
    }
}

pub fn resolve_typefn(impls: &Vec<(String, Type)>, t: Type) -> Option<String> {
    for (name, ty) in impls {
        // Try to unify the impl type with id type
        let subs = HashMap::new();
        let gen_ty = ty.clone().fresh();

        if let Some(subs) = unify(t.clone(), gen_ty.clone(), subs) {
            if apply_unifier(gen_ty, &subs) == t {
                return Some(name.clone());
            }
        }
    }

    None
}

pub fn gen_impl_map(
    mods: &HashMap<String, crate::resolve::Module>,
    trees: &HashMap<String, ParseTree>,
) -> HashMap<String, Vec<(String, Type)>> {
    // Generate a new name for each typefn impl, adding its type and body to the funcs
    // Additionally create a map of each (typefn, type) to the new name
    let mut impl_map = HashMap::<String, Vec<(String, Type)>>::new();

    for (_, module) in mods {
        // Make sure there is at least an empty list for every typefunction
        for tfun in module.pub_typefn.iter() {
            if !impl_map.contains_key(tfun.0) {
                impl_map.insert(tfun.0.clone(), vec![]);
            }
        }

        for (new_name, _) in module.pub_impls.iter() {
            let ns = new_name.rsplit_once("/").unwrap().0;
            let name = new_name.rsplit_once("$").unwrap().0;

            let (_, QualType(_, real_type)) = &trees[ns].typedecls[new_name];

            if let Some(impls) = impl_map.get_mut(name) {
                impls.push((new_name.clone(), real_type.clone()));
            } else {
                impl_map.insert(
                    name.to_string(),
                    vec![(new_name.clone(), real_type.clone())],
                );
            }

            // trees[n].typedecls.insert(new_name.clone(), (real_type));
            // typedecls.insert(new_name.clone(), real_type);
            // tree.funcs.insert(new_name, imp.body);
        }
    }

    impl_map
}
