use std::collections::{HashMap, HashSet, VecDeque};

use crate::parse_tree::{
    Constraint, DataDecl, Expression, FunctionDef, Impl, ParseTree, Pattern, QualType, Type,
    TypeCons, TypeFun,
};

/// A package of all public information about a module.
///
/// Useful for resolving and canonicalizing names
pub struct Module {
    /// map from local name to type
    pub pub_data: HashMap<String, DataDecl>,
    pub pub_cons: HashMap<String, Type>,

    pub pub_decls: HashMap<String, QualType>,
    pub pub_gens: HashMap<String, (QualType, Vec<FunctionDef>)>,

    pub pub_typefn: HashMap<String, TypeFun>,
    pub pub_impls: HashMap<String, Vec<Type>>,
}

impl ParseTree {
    // canonicalize all new defined names in the tree
    // by prefixing with this modules import path.
    //
    // After this step all names should be prefixed with
    // this module path or another module path. All identifiers
    // in functions should be unique
    //
    // return a module struct that contains all publicly
    // importable names and the associated data with them
    pub fn canonicalize(&mut self, prefix: &str) -> Module {
        let local_typefuns = self.typefuns.keys().cloned().collect();

        let local_datadecls = self
            .types
            .iter()
            .map(|dd| dd.0.clone())
            .collect::<HashSet<_>>();

        let local_cons: HashSet<String> = self
            .types
            .iter()
            .map(|(_, dd)| dd.2.iter().map(|c| c.name.clone()))
            .flatten()
            .collect();

        let local_decls = self.typedecls.keys().cloned().collect();

        // canonicalize data declarations
        self.types = self
            .types
            .clone()
            .into_iter()
            .map(|(_, mut dd)| {
                dd.canonicalize(prefix, &local_datadecls, &self.imports);
                (dd.0.clone(), dd)
            })
            .collect();

        // canonicalize type declarations
        self.typedecls = self
            .typedecls
            .clone()
            .into_iter()
            .map(|(name, mut td)| {
                td.canonicalize(prefix, &local_datadecls, &local_typefuns, &self.imports);
                (format!("{prefix}.{name}"), td)
            })
            .collect();

        // canonicalize expressions
        self.funcs = self
            .funcs
            .clone()
            .into_iter()
            .map(|(name, mut funcs)| {
                funcs.iter_mut().for_each(|f| {
                    f.canonicalize(
                        prefix,
                        &local_decls,
                        &local_cons,
                        &local_typefuns,
                        &self.imports,
                    )
                });
                (format!("{prefix}.{name}"), funcs)
            })
            .collect();

        self.defs = self
            .defs
            .clone()
            .into_iter()
            .map(|(name, mut def)| {
                def.canonicalize(
                    prefix,
                    &local_decls,
                    &local_cons,
                    &local_typefuns,
                    &HashSet::new(),
                    &self.imports,
                );
                (format!("{prefix}.{name}"), def)
            })
            .collect();

        // canonicalize type functions
        self.typefuns = self
            .typefuns
            .clone()
            .into_iter()
            .map(|(name, mut tf)| {
                tf.name = format!("{prefix}.{name}");
                tf.ty.canonicalize(prefix, &local_datadecls, &self.imports);
                (format!("{prefix}.{name}"), tf)
            })
            .collect();

        // canonicalize impls
        for impll in self.impls.iter_mut() {
            impll.canonicalize(
                prefix,
                &local_datadecls,
                &local_typefuns,
                &local_decls,
                &local_cons,
                &self.imports,
            );
        }

        Module {
            pub_data: self.types.clone().into_iter().collect(),
            pub_cons: self
                .types
                .iter()
                .map(|(_, dd)| dd.2.iter().map(|c| (c.name.clone(), c.args.clone())))
                .flatten()
                .collect(),
            pub_decls: self
                .typedecls
                .clone()
                .into_iter()
                .filter(|(_, t)| !t.is_generic())
                .collect(),
            pub_gens: self
                .typedecls
                .clone()
                .into_iter()
                .filter(|(_, t)| t.is_generic())
                .map(|(name, t)| (name.clone(), (t, self.funcs[&name].clone())))
                .collect(),
            pub_typefn: self.typefuns.clone(),
            pub_impls: self
                .impls
                .clone()
                .into_iter()
                .map(|i| (i.fn_name, i.args))
                .collect(),
        }
    }

    // Now that all names are canon, copy all the informaion into this
    // tree that is necessary to compile without referencing any
    // other modules.
    //
    // All datadecls get copied over
    // All non-generic typedecls get copied over
    // All generic typedecls get their type and bodies copied,
    //    and then their body is recursively resolved
    // All typefuns get copied over
    // Impls are handled globally, so, no need to worry about it, only
    //    need to resolve the body with non-impl calls
    //    (I'm sure this won't come back to haunt me)
    pub fn resolve(&mut self, me: &str, mods: &HashMap<String, Module>) {
        // Get the names of types from other modules used in our types
        let mut imported_data = HashSet::new();
        let mut imported_idents = VecDeque::new();

        // Basically two steps:
        // 1. aggregate all the names that we use but do not provide
        // 2. copy over the necessary data based on each name

        for (_, dd) in self.types.iter() {
            imported_data.extend(dd.imported(me));
        }

        for (_, td) in self.typedecls.iter() {
            let (types, decls) = td.imported(me);
            imported_data.extend(types);
            imported_idents.extend(decls);
        }

        for (_, funcs) in self.funcs.iter() {
            for func in funcs {
                imported_idents.extend(func.imported(me));
            }
        }

        for (_, defs) in self.defs.iter() {
            imported_idents.extend(defs.imported(me))
        }

        for TypeFun { ty, .. } in self.typefuns.values() {
            imported_data.extend(ty.imported(me));
        }

        for Impl { args, body, .. } in self.impls.iter() {
            for arg in args {
                imported_data.extend(arg.imported(me));
            }

            for func in body {
                imported_idents.extend(func.imported(me));
            }
        }

        // Now the secret step 1.5: add the impl types and bodies
        // to the tree
        for Impl {
            fn_name: new_name,
            args,
            body,
            ..
        } in self.impls.clone().into_iter()
        {
            let ns = new_name.rsplit_once(".").unwrap().0;
            let tf = new_name.rsplit_once("$").unwrap().0;

            let TypeFun { name, ty, vars } = mods[ns].pub_typefn[tf].clone();

            // substitutions to go from impl to real type
            let mut subs = HashMap::new();
            for (var, arg) in vars.iter().zip(args.iter()) {
                subs.insert(var.clone(), arg.clone());
            }

            // Get the type of the typefun
            let ty = crate::mir::typefn_type(TypeFun {
                name: name.clone(),
                ty: ty.clone(),
                vars: vec![],
            });
            let real_type = ty.replace_all(&subs);

            self.typedecls
                .insert(new_name.clone(), QualType(vec![], real_type));
            self.funcs.insert(new_name, body);
        }

        // Now step two:
        // imported_data is pretty simple, it will always be
        //     a declared type in its module.
        // imported_idents is a littler harder, it can either
        //    be a regular function, a generic function, or
        //    a typefunction. generic functions need to be
        //    recursively resolved in a breadth first manner
        //    to account for cycles
        self.import_idents = imported_idents.clone().into_iter().collect();

        for name in imported_data {
            let mod_name = name.rsplit_once(".").unwrap().0;
            let modu = &mods[mod_name];

            self.types
                .insert(name.clone(), modu.pub_data[&name].clone());
        }

        while let Some(name) = imported_idents.pop_front() {
            let mod_name = name.rsplit_once(".").unwrap().0;
            let modu = &mods[mod_name];

            if let Some(_) = modu.pub_cons.get(&name) {
                // cons is a no op since the constructor is automatically
                // created from the data definition
            } else if let Some(decl) = modu.pub_decls.get(&name) {
                self.typedecls.insert(name, decl.clone());
            } else if let Some(tfun) = modu.pub_typefn.get(&name) {
                self.typefuns.insert(name, tfun.clone());
            } else if let Some((ty, body)) = modu.pub_gens.get(&name) {
                if !self.typedecls.contains_key(&name) {
                    self.typedecls.insert(name.clone(), ty.clone());

                    for f in body {
                        imported_idents.extend(f.imported(me))
                    }
                }
            }
        }
    }
}

impl DataDecl {
    /// Convert datadecls to their canon names
    fn canonicalize(
        &mut self,
        me: &str,
        types: &HashSet<String>,   // set of local data decl names
        imports: &HashSet<String>, // set of imported module names
    ) {
        // the name just gets hit with the prefix of this module
        self.0 = format!("{me}.{}", self.0);

        self.2
            .iter_mut()
            .for_each(|tc| tc.canonicalize(me, types, &imports));
    }

    // find all the imported types
    fn imported(&self, me: &str) -> Vec<String> {
        self.2.iter().map(|tc| tc.imported(me)).flatten().collect()
    }
}

impl TypeCons {
    fn canonicalize(&mut self, me: &str, types: &HashSet<String>, imports: &HashSet<String>) {
        self.name = format!("{me}.{}", self.name);
        self.args.canonicalize(me, types, imports);
    }

    fn imported(&self, me: &str) -> Vec<String> {
        self.args.imported(me)
    }
}

impl Type {
    fn canonicalize(&mut self, me: &str, types: &HashSet<String>, imports: &HashSet<String>) {
        match self {
            Type::Ident(i) => {
                if types.contains(i) {
                    *i = format!("{me}.{}", i);
                } else if let Some((ns, _)) = i.rsplit_once(".") {
                    if !imports.contains(ns) {
                        panic!("type uses unimported ns {ns} from {i}")
                    }
                }
            }
            Type::ForAll(_, _, _) => panic!(),
            Type::Generic(ts, t) => {
                t.canonicalize(me, types, imports);
                ts.iter_mut()
                    .for_each(|t| t.canonicalize(me, types, imports));
            }
            Type::Arrow(a, b) => {
                a.canonicalize(me, types, imports);
                b.canonicalize(me, types, imports);
            }
            Type::Tuple(ts) => {
                ts.iter_mut()
                    .for_each(|t| t.canonicalize(me, types, imports));
            }
            _ => {}
        }
    }

    // check if a canonicalized type is generic
    fn is_generic(&self) -> bool {
        match self {
            Type::Ident(i) => !i.contains("."),
            Type::ForAll(_, _, _) => panic!(),
            Type::Generic(ts, t) => ts.iter().any(|t| t.is_generic()) || t.is_generic(),
            Type::Arrow(a, b) => a.is_generic() || b.is_generic(),
            Type::Tuple(ts) => ts.iter().any(|t| t.is_generic()),
            _ => false,
        }
    }

    fn imported(&self, me: &str) -> Vec<String> {
        match self {
            Type::Ident(i) if i.contains(".") && !i.starts_with(me) => vec![i.clone()],
            Type::ForAll(_, _, _) => panic!(),
            Type::Generic(ts, t) => ts
                .iter()
                .chain(vec![*t.clone()].iter())
                .map(|t| t.imported(me))
                .flatten()
                .collect(),
            Type::Arrow(a, b) => vec![a]
                .iter()
                .chain(vec![b].iter())
                .map(|t| t.imported(me))
                .flatten()
                .collect(),
            Type::Tuple(ts) => ts.iter().map(|t| t.imported(me)).flatten().collect(),
            _ => vec![],
        }
    }
}

impl QualType {
    /// Convert constraint names to their canonical form
    /// Convert type idents to their canonical form
    fn canonicalize(
        &mut self,
        me: &str,
        types: &HashSet<String>,
        typefuns: &HashSet<String>,
        imports: &HashSet<String>,
    ) {
        let QualType(cons, t) = self;

        cons.iter_mut()
            .for_each(|c| c.canonicalize(me, types, typefuns, imports));
        t.canonicalize(me, types, imports);
    }

    // Check if a canonicalized QualType has generic params
    fn is_generic(&self) -> bool {
        self.1.is_generic()
    }

    fn imported(&self, me: &str) -> (Vec<String>, Vec<String>) {
        let imported_decls = self.0.iter().map(|c| c.imported(me)).flatten().collect();
        let imported_types = self.1.imported(me);

        (imported_types, imported_decls)
    }
}

impl Constraint {
    fn canonicalize(
        &mut self,
        me: &str,
        types: &HashSet<String>,
        typefuns: &HashSet<String>,
        imports: &HashSet<String>,
    ) {
        let Constraint(name, ts) = self;

        if typefuns.contains(name) {
            *name = format!("{me}.{name}");
        } else if let Some((ns, _)) = name.rsplit_once(".") {
            if !imports.contains(ns) {
                panic!()
            }
        } else {
            panic!()
        }

        ts.iter_mut()
            .for_each(|t| t.canonicalize(me, types, imports));
    }

    fn imported(&self, me: &str) -> Vec<String> {
        self.1.iter().map(|t| t.imported(me)).flatten().collect()
    }
}

impl Impl {
    fn canonicalize(
        &mut self,
        me: &str,
        types: &HashSet<String>,
        typefuns: &HashSet<String>,
        decls: &HashSet<String>,
        cons: &HashSet<String>,
        imports: &HashSet<String>,
    ) {
        // Every impl gets a unique global name based on their typefunction name
        self.fn_name = crate::gen_var(&if typefuns.contains(&self.fn_name) {
            format!("{me}.{}$", self.fn_name)
        } else {
            format!("{}$", self.fn_name)
        });

        self.args
            .iter_mut()
            .for_each(|t| t.canonicalize(me, types, imports));

        self.body
            .iter_mut()
            .for_each(|fd| fd.canonicalize(me, decls, cons, typefuns, imports));
    }
}

impl FunctionDef {
    fn canonicalize(
        &mut self,
        me: &str,
        decls: &HashSet<String>,
        cons: &HashSet<String>,
        typefuns: &HashSet<String>,
        imports: &HashSet<String>,
    ) {
        self.name = format!("{me}.{}", self.name);

        self.args.canonicalize(me, cons, imports);
        let mut locals = HashSet::new();
        locals.extend(self.args.free_vars());

        self.body
            .canonicalize(me, decls, cons, typefuns, imports, &locals);
    }

    fn imported(&self, me: &str) -> Vec<String> {
        self.args
            .imported(me)
            .into_iter()
            .chain(self.body.imported(me).into_iter())
            .collect()
    }
}

impl Pattern {
    fn canonicalize(&mut self, me: &str, cons: &HashSet<String>, imports: &HashSet<String>) {
        match self {
            Pattern::Cons(f, args, _) => {
                if cons.contains(f) {
                    *f = format!("{me}.{f}");
                } else if let Some((ns, _)) = f.rsplit_once(".") {
                    if !imports.contains(ns) {
                        panic!()
                    }
                } else {
                    panic!()
                }

                args.canonicalize(me, cons, imports);
            }
            Pattern::Tuple(ps, _) => {
                ps.iter_mut()
                    .for_each(|p| p.canonicalize(me, cons, imports));
            }
            _ => {}
        }
    }

    fn imported(&self, me: &str) -> Vec<String> {
        match self {
            Pattern::Cons(f, args, _) => {
                let mut rest = args.imported(me);

                if !f.starts_with(me) {
                    rest.push(f.clone());
                }

                rest
            }
            Pattern::Tuple(ps, _) => ps.iter().map(|p| p.imported(me)).flatten().collect(),
            _ => vec![],
        }
    }
}

impl Expression {
    fn canonicalize(
        &mut self,
        me: &str,
        decls: &HashSet<String>,
        cons: &HashSet<String>,
        typefuns: &HashSet<String>,
        imports: &HashSet<String>,
        locals: &HashSet<String>,
    ) {
        match self {
            Expression::Identifier(i) => {
                if decls.contains(i) || cons.contains(i) || typefuns.contains(i) {
                    *i = format!("{me}.{i}");
                } else if let Some((ns, _)) = i.rsplit_once(".") {
                    if !imports.contains(ns) {
                        panic!("namespace {ns} not imported")
                    }
                } else if !locals.contains(i) {
                    panic!("undeclared variable {i}");
                }
            }
            Expression::Let(p, e, body) => {
                p.canonicalize(me, cons, imports);
                e.canonicalize(me, decls, cons, typefuns, imports, locals);

                let mut locals = locals.clone();
                locals.extend(p.free_vars());
                body.canonicalize(me, decls, cons, typefuns, imports, &locals);
            }
            Expression::Tuple(es) => {
                es.iter_mut()
                    .for_each(|e| e.canonicalize(me, decls, cons, typefuns, imports, locals));
            }
            Expression::If(cond, a, b) => {
                cond.canonicalize(me, decls, cons, typefuns, imports, locals);
                a.canonicalize(me, decls, cons, typefuns, imports, locals);
                b.canonicalize(me, decls, cons, typefuns, imports, locals);
            }
            Expression::Match(e, eps) => {
                e.canonicalize(me, decls, cons, typefuns, imports, locals);

                for (p, e) in eps {
                    p.canonicalize(me, cons, imports);

                    let mut locals = locals.clone();
                    locals.extend(p.free_vars());
                    e.canonicalize(me, decls, cons, typefuns, imports, &locals);
                }
            }
            Expression::Call(a, b) => {
                a.canonicalize(me, decls, cons, typefuns, imports, locals);
                b.canonicalize(me, decls, cons, typefuns, imports, locals);
            }
            Expression::Lambda(p, e) => {
                p.canonicalize(me, cons, imports);

                let mut locals = locals.clone();
                locals.extend(p.free_vars());
                e.canonicalize(me, decls, cons, typefuns, imports, &locals);
            }
            _ => {}
        }
    }

    fn imported(&self, me: &str) -> Vec<String> {
        match self {
            Expression::Identifier(i) => {
                if i.contains(".") && !i.starts_with(me) {
                    vec![i.clone()]
                } else {
                    vec![]
                }
            }
            Expression::Let(p, e, body) => {
                let mut r = p.imported(me);
                r.extend(e.imported(me));
                r.extend(body.imported(me));
                r
            }
            Expression::Tuple(es) => es.iter().map(|e| e.imported(me)).flatten().collect(),
            Expression::If(cond, a, b) => {
                let mut r = cond.imported(me);
                r.extend(a.imported(me));
                r.extend(b.imported(me));
                r
            }
            Expression::Match(e, eps) => {
                let mut r = e.imported(me);

                for (p, e) in eps {
                    r.extend(p.imported(me));
                    r.extend(e.imported(me));
                }
                r
            }
            Expression::Call(a, b) => {
                let mut r = a.imported(me);
                r.extend(b.imported(me));
                r
            }
            Expression::Lambda(p, e) => {
                let mut r = p.imported(me);
                r.extend(e.imported(me));
                r
            }
            _ => vec![],
        }
    }
}
