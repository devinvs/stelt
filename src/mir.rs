use std::collections::HashMap;
use std::collections::HashSet;

use crate::parse_tree::{DataDecl, Expression, ParseTree, Pattern, Type, TypeCons};

use crate::unify::apply_unifier;
use crate::unify::unify;
use crate::unify::Term;

type Theta = HashMap<Term<String>, Term<String>>;

#[derive(Debug)]
pub struct MIRTree {
    pub external: HashSet<String>,
    pub types: Vec<(String, DataDecl)>,
    pub typedefs: HashMap<String, Type>,
    pub structs: HashMap<String, HashMap<String, Type>>,
    pub funcs: HashMap<String, MIRExpression>,
    pub defs: HashMap<String, MIRExpression>,
    pub impl_map: HashMap<String, Vec<(String, Type)>>,

    pub constructors: HashMap<String, Type>,
    pub declarations: HashMap<String, Type>,

    pub imports: HashSet<String>,
    pub import_funcs: HashMap<String, Type>,
}

impl MIRTree {
    pub fn from(mut tree: ParseTree) -> Self {
        let mut typedefs = tree.typedefs;
        let mut declarations = HashMap::new();

        // Type functions type check as a forall type
        for (name, typefn) in tree.typefuns.clone() {
            let t = match typefn.ty {
                Type::ForAll(mut vars, t) => {
                    vars.extend(typefn.vars);
                    Type::ForAll(vars, t)
                }
                t => Type::ForAll(typefn.vars, Box::new(t)),
            };
            declarations.insert(name, t);
        }

        // Generate a new name for each typefn impl, adding its type and body to the funcs
        // Additionally create a map of each (typefn, type) to the new name
        let mut impl_map = HashMap::<String, Vec<(String, Type)>>::new();
        for imp in tree.impls {
            let typefn = tree.typefuns.get(&imp.fn_name).unwrap();
            let new_name = crate::gen_var(&format!("{}$", imp.fn_name));

            let mut subs = HashMap::new();
            for (var, arg) in typefn.vars.iter().zip(imp.args.iter()) {
                subs.insert(var.clone(), arg.clone());
            }

            let real_type = typefn.ty.clone().replace_all(&subs);
            if let Some(impls) = impl_map.get_mut(&typefn.name) {
                impls.push((new_name.clone(), real_type.clone()));
            } else {
                impl_map.insert(
                    typefn.name.clone(),
                    vec![(new_name.clone(), real_type.clone())],
                );
            }

            typedefs.insert(new_name.clone(), real_type);
            tree.funcs.insert(new_name, imp.body);
        }

        // Add all user defined type definitions to declaratiosn
        for (name, t) in typedefs.iter() {
            declarations.insert(name.clone(), t.clone());
        }

        // Add all type constructors to conss
        let mut constructors = HashMap::new();
        let mut structs = HashMap::new();

        for (name, decl) in tree.types.iter() {
            match decl {
                DataDecl::Sum(_, args, cons) => {
                    for cons in cons {
                        let outt = if args.len() == 0 {
                            Box::new(Type::Ident(name.clone()))
                        } else {
                            Box::new(Type::Generic(
                                args.clone().into_iter().map(|s| Type::Ident(s)).collect(),
                                Box::new(Type::Ident(name.clone())),
                            ))
                        };

                        constructors.insert(
                            cons.name.clone(),
                            Type::ForAll(
                                args.clone(),
                                Box::new(Type::Arrow(Box::new(cons.args.clone()), outt)),
                            ),
                        );
                    }
                }
                DataDecl::Product(_, args, members) => {
                    // Add an entry into the structs map
                    let mut m = HashMap::new();
                    members.iter().for_each(|(n, t)| {
                        m.insert(n.clone(), t.clone());
                    });

                    structs.insert(name.clone(), m);

                    // add constructor
                    let outt = if args.len() == 0 {
                        Box::new(Type::Ident(name.clone()))
                    } else {
                        Box::new(Type::Generic(
                            args.clone().into_iter().map(|s| Type::Ident(s)).collect(),
                            Box::new(Type::Ident(name.clone())),
                        ))
                    };

                    let inputt = members
                        .into_iter()
                        .map(|(_, t)| t.clone())
                        .collect::<Vec<_>>();

                    let inputt = match inputt.len() {
                        0 => Box::new(Type::Unit),
                        1 => Box::new(inputt.into_iter().next().unwrap()),
                        _ => Box::new(Type::Tuple(inputt)),
                    };

                    constructors.insert(
                        name.clone(),
                        Type::ForAll(args.clone(), Box::new(Type::Arrow(inputt, outt))),
                    );
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
            types: tree.types,
            typedefs,
            funcs,
            defs,
            constructors,
            declarations,
            structs,
            impl_map,
            imports: tree.imports,
            import_funcs: tree.import_funcs,
        }
    }

    pub fn with_concrete_types(mut self) -> Self {
        let mut generic_decls = HashMap::new();
        let mut concrete_decls = HashMap::new();

        // split out generic typedecls from the concrete ones
        for (name, t) in self.typedefs {
            match t {
                Type::ForAll(args, inner) => {
                    if args.len() == 0 {
                        concrete_decls.insert(name, *inner);
                    } else {
                        generic_decls.insert(name, Type::ForAll(args, inner));
                    }
                }
                a => {
                    concrete_decls.insert(name, a);
                }
            }
        }

        let mut concrete_funcs = HashMap::new();

        let cons = self
            .types
            .iter()
            .filter_map(|t| match &t.1 {
                DataDecl::Product(..) => None,
                DataDecl::Sum(_, _, cons) => {
                    Some(cons.iter().map(|tc| tc.name.clone()).collect::<Vec<_>>())
                }
            })
            .flatten()
            .collect();

        // for every concrete function type extract the calls to generic functions
        // and add them to the concrete functions as well
        for name in concrete_decls.clone().into_keys() {
            if let Some(body) = self.funcs.get(&name) {
                let body = body.clone().resolve_typefn(&self.impl_map);
                let (f, calls) = body.extract_calls(&generic_decls, &cons);
                concrete_funcs.insert(name.clone(), f);

                for (name, newname, ty) in calls {
                    // add concrete function prototype for new function
                    concrete_decls.insert(newname.clone(), ty.clone());

                    let oldty = generic_decls[&name].clone();
                    let subs = oldty.get_generic_subs(&ty);

                    if let Some(f) = self.funcs.get(&name) {
                        // add new function body substituting generic types for concrete types
                        let f = f.clone().sub_types(&subs).resolve_typefn(&self.impl_map);
                        concrete_funcs.insert(newname, f);
                    }
                }
            }
        }

        let mut generic_types = HashMap::new();
        let mut concrete_types = HashMap::new();

        // split out the generic type prototypes and the concrete types
        for (name, t) in self.types {
            let argc = match t.clone() {
                DataDecl::Sum(_, args, _) => args.len(),
                DataDecl::Product(_, args, _) => args.len(),
            };

            if argc == 0 {
                concrete_types.insert(name, t);
            } else {
                generic_types.insert(name, t);
            }
        }

        // For each declared type replace generics with concrete instances
        for (_, t) in concrete_decls.iter_mut() {
            let (newt, concs) = t.clone().extract_generics(&generic_types);
            for conc in concs {
                concrete_types.insert(conc.name(), conc);
            }
            *t = newt;
        }

        // finally, for every concrete type extract the generics from their members and constructors
        let mut other_concretes = HashMap::new();
        for (_, t) in concrete_types.iter_mut() {
            *t = match t {
                DataDecl::Product(n, v, mems) => {
                    let mems = mems
                        .into_iter()
                        .map(|(name, t)| {
                            let (newt, concs) = t.clone().extract_generics(&generic_types);
                            for conc in concs {
                                other_concretes.insert(conc.name(), conc);
                            }
                            (name.clone(), newt)
                        })
                        .collect();

                    DataDecl::Product(n.clone(), v.clone(), mems)
                }
                DataDecl::Sum(n, v, cons) => {
                    let cons = cons
                        .into_iter()
                        .map(|TypeCons { name, args }| {
                            let (newt, concs) = args.clone().extract_generics(&generic_types);
                            for conc in concs {
                                other_concretes.insert(conc.name(), conc);
                            }
                            TypeCons {
                                name: name.clone(),
                                args: newt,
                            }
                        })
                        .collect();

                    DataDecl::Sum(n.clone(), v.clone(), cons)
                }
            };
        }

        concrete_types.extend(other_concretes);
        // change type constructor names to have their type as a prefix

        for (_, data) in concrete_types.iter_mut() {
            let name = data.name();
            match data {
                DataDecl::Product(..) => {}
                DataDecl::Sum(_, _, cons) => {
                    for cons in cons.iter_mut() {
                        let newname = format!("{}${}$", cons.name, name);
                        cons.name = newname;
                    }
                }
            }
        }

        self.types = concrete_types.into_iter().collect();
        self.typedefs = concrete_decls;
        self.funcs = concrete_funcs;

        // remove recursion from recursive types with boxing
        let data = self.types.clone();
        for (name, d) in data.into_iter() {
            let d = d.remove_recursion(&name, &mut self.types);
            *self
                .types
                .iter_mut()
                .find(|(n, _)| *n == name)
                .map(|(_, a)| a)
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

    /// A list of expressions
    List(Vec<MIRExpression>, Option<Type>),

    /// Test a list of patterns against an expression, returning the expression that matches
    Match(
        Box<MIRExpression>,
        Vec<(Pattern, MIRExpression)>,
        Option<Type>,
    ),

    /// Call the function with args
    /// Can be a global function, a lambda, or a constructor
    Call(Box<MIRExpression>, Box<MIRExpression>, Option<Type>),

    /// Get the member of a struct
    Member(Box<MIRExpression>, String, Option<Type>),

    /// A lambda expression with pattern args and an expression body
    Lambda1(Option<String>, Box<MIRExpression>, Option<Type>),

    // Constant Fields
    Num(u64, Option<Type>), // A Number Literal
    Unit(Option<Type>),
}

impl MIRExpression {
    fn sub_types(self, subs: &HashMap<String, Type>) -> Self {
        let t = self.ty().replace_all(subs);

        match self {
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
            MIRExpression::List(es, _) => {
                MIRExpression::List(es.into_iter().map(|e| e.sub_types(subs)).collect(), Some(t))
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
            MIRExpression::Member(e, mem, _) => {
                MIRExpression::Member(Box::new(e.sub_types(subs)), mem, Some(t))
            }
        }
    }

    fn from(tree: Expression, cons: &HashMap<String, Type>) -> Self {
        match tree {
            Expression::Namespace(..) => panic!(),
            Expression::Num(n) => Self::Num(n, None),
            Expression::Unit => Self::Unit(Some(Type::Unit)),
            Expression::Identifier(i) => Self::Identifier(i, None),
            Expression::ExprList(es) => Self::List(
                es.into_iter()
                    .map(|e| MIRExpression::from(e, cons))
                    .collect(),
                None,
            ),
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
            Expression::Member(t, variant) => {
                if let Expression::Identifier(t) = *t {
                    if cons.contains_key(&format!("{t}.{variant}")) {
                        MIRExpression::Identifier(format!("{t}.{variant}"), None)
                    } else {
                        MIRExpression::Member(
                            Box::new(MIRExpression::Identifier(t, None)),
                            variant,
                            None,
                        )
                    }
                } else {
                    MIRExpression::Member(Box::new(MIRExpression::from(*t, cons)), variant, None)
                }
            }
            Expression::Lambda(pat, body) => match pat.trans_cons(cons) {
                Pattern::Var(s, _) => {
                    Self::Lambda1(Some(s), Box::new(MIRExpression::from(*body, cons)), None)
                }
                Pattern::Tuple(ps, _) => {
                    let mut i = ps.into_iter();
                    let first = i.next().unwrap();
                    let rest: Vec<_> = i.collect();

                    if rest.is_empty() {
                        let l = Expression::Lambda(first, body);
                        MIRExpression::from(l, cons)
                    } else {
                        let l = Expression::Lambda(Pattern::Tuple(rest, None), body);
                        let l = Expression::Lambda(first, Box::new(l));
                        MIRExpression::from(l, cons)
                    }
                }
                Pattern::Unit(..) => {
                    Self::Lambda1(None, Box::new(MIRExpression::from(*body, cons)), None)
                }
                _ => panic!(),
            },
            Expression::Let(pat, val, body) => Self::Match(
                Box::new(MIRExpression::from(*val, cons)),
                vec![(pat.trans_cons(cons), MIRExpression::from(*body, cons))],
                None,
            ),
            Expression::If(cond, then, els) => Self::Match(
                Box::new(MIRExpression::from(*cond, cons)),
                vec![
                    (
                        Pattern::Cons(
                            "True".into(),
                            Box::new(Pattern::Unit(Some(Type::Unit))),
                            None,
                        ),
                        MIRExpression::from(*then, cons),
                    ),
                    (
                        Pattern::Cons(
                            "False".into(),
                            Box::new(Pattern::Unit(Some(Type::Unit))),
                            None,
                        ),
                        MIRExpression::from(*els, cons),
                    ),
                ],
                None,
            ),
        }
    }

    fn resolve_typefn(self, impl_map: &HashMap<String, Vec<(String, Type)>>) -> Self {
        match self {
            Self::Identifier(s, Some(t)) => {
                if let Some(impls) = impl_map.get(&s) {
                    Self::Identifier(
                        resolve_typefn(impls, t.clone()).expect(&format!(
                            "Could not find impl for typefn: {s} of type {t:?}"
                        )),
                        Some(t),
                    )
                } else {
                    Self::Identifier(s, Some(t))
                }
            }
            Self::List(exprs, t) => Self::List(
                exprs
                    .into_iter()
                    .map(|e| e.resolve_typefn(impl_map))
                    .collect(),
                t,
            ),
            Self::Tuple(exprs, t) => Self::Tuple(
                exprs
                    .into_iter()
                    .map(|e| e.resolve_typefn(impl_map))
                    .collect(),
                t,
            ),
            Self::Match(x, pats, t) => Self::Match(
                Box::new(x.resolve_typefn(impl_map)),
                pats.into_iter()
                    .map(|(p, e)| (p, e.resolve_typefn(impl_map)))
                    .collect(),
                t,
            ),
            Self::Call(m, n, t) => Self::Call(
                Box::new(m.resolve_typefn(impl_map)),
                Box::new(n.resolve_typefn(impl_map)),
                t,
            ),
            Self::Lambda1(x, m, t) => Self::Lambda1(x, Box::new(m.resolve_typefn(impl_map)), t),
            Self::Member(x, m, t) => Self::Member(Box::new(x.resolve_typefn(impl_map)), m, t),
            a => a,
        }
    }

    pub fn ty(&self) -> Type {
        match self {
            Self::Identifier(_, t) => t,
            Self::Num(_, t) => t,
            Self::Unit(t) => t,
            Self::List(_, t) => t,
            Self::Tuple(_, t) => t,
            Self::Match(_, _, t) => t,
            Self::Call(_, _, t) => t,
            Self::Lambda1(_, _, t) => t,
            Self::Member(_, _, t) => t,
        }
        .clone()
        .expect(&format!("{:?}", self))
    }

    pub fn set_type(&mut self, ty: Type) {
        match self {
            Self::Identifier(_, t) => *t = Some(ty),
            Self::Num(_, t) => *t = Some(ty),
            Self::Unit(t) => *t = Some(ty),
            Self::List(_, t) => *t = Some(ty),
            Self::Tuple(_, t) => *t = Some(ty),
            Self::Match(_, _, t) => *t = Some(ty),
            Self::Call(_, _, t) => *t = Some(ty),
            Self::Lambda1(_, _, t) => *t = Some(ty),
            Self::Member(_, _, t) => *t = Some(ty),
        }
    }

    pub fn apply(&mut self, subs: &Theta) {
        let term = self.ty().to_term();
        let unterm = apply_unifier(term, subs);
        self.set_type(Type::from_term(unterm));

        match self {
            Self::List(a, _) => a.iter_mut().for_each(|e| e.apply(subs)),
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
            Self::Member(a, ..) => {
                a.apply(subs);
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
                    let newname = format!("{name}${}$", crate::id());

                    (
                        MIRExpression::Identifier(newname.clone(), t.clone()),
                        vec![(name, newname, t.unwrap())],
                    )
                } else if cons.contains(&name) {
                    let out_t = match t.clone().unwrap() {
                        Type::Arrow(_, t) => t,
                        _ => panic!(),
                    };
                    let newname = format!("{name}${}$", out_t.to_string());

                    (MIRExpression::Identifier(newname, t), vec![])
                } else {
                    (MIRExpression::Identifier(name, t), vec![])
                }
            }
            MIRExpression::List(es, t) => {
                let mut v = vec![];
                let mut newes = vec![];

                for e in es {
                    let (e, gens) = e.extract_calls(generics, cons);
                    newes.push(e);
                    v.extend(gens);
                }

                (MIRExpression::List(newes, t), v)
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
            MIRExpression::Member(e, mem, t) => {
                let (e, gens) = e.extract_calls(generics, cons);
                (MIRExpression::Member(Box::new(e), mem, t), gens)
            }
            MIRExpression::Match(e, ps, t) => {
                // I don't think that we need to check the patterns, but I'm not entirely sure
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
                let newname = format!("{name}${}$", t.as_ref().unwrap().to_string());

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
            Pattern::Any(..) => Pattern::Any(Some(t)),
            Pattern::Namespace(..) => panic!(),
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
        let term = self.ty().to_term();
        let unterm = apply_unifier(term, subs);
        self.set_type(Type::from_term(unterm));

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
    fn fresh(self) -> Self {
        let mut i = 0;

        match self {
            Type::ForAll(vars, inner) => {
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
        if let Type::ForAll(vars, t) = self {
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
            Type::ForAll(a, b) => {
                let (t, ts) = b.extract_generics(generics);
                (Type::ForAll(a, Box::new(t)), ts)
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

    fn replace_all(mut self, subs: &HashMap<String, Type>) -> Self {
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
            Type::Arrow(a, b) => {
                let a = a.replace(from, to);
                let b = b.replace(from, to);

                Type::Arrow(Box::new(a), Box::new(b))
            }
            Type::ForAll(a, b) => Type::ForAll(a, Box::new(b.replace(from, to))),
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
            DataDecl::Sum(_, args, cons) => {
                let mut new_cons = vec![];

                for con in cons {
                    let mut con = con.clone();

                    for (arg, val) in args.iter().zip(vals.iter()) {
                        con = con.replace(arg, val);
                    }

                    new_cons.push(con);
                }

                DataDecl::Sum(name, vec![], new_cons)
            }
            DataDecl::Product(_, args, mems) => {
                let mut new_mems = vec![];

                for (mem_n, mut mem) in mems.clone() {
                    for (arg, val) in args.iter().zip(vals.iter()) {
                        mem = mem.replace(arg, val);
                    }
                    new_mems.push((mem_n, mem));
                }

                DataDecl::Product(name, vec![], new_mems)
            }
        }
    }

    fn name(&self) -> String {
        match self {
            Self::Sum(n, _, _) => n,
            Self::Product(n, _, _) => n,
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

        if let Some(subs) = unify(t.to_term(), gen_ty.to_term(), subs) {
            if apply_unifier(gen_ty.to_term(), &subs) == t.to_term() {
                return Some(name.clone());
            }
        }
    }

    None
}
