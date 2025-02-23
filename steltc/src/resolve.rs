use std::collections::{HashMap, HashSet, VecDeque};

use crate::parse_tree::{
    Constraint, DataDecl, Expression, FunctionDef, Impl, ParseTree, Pattern, QualType, Type,
    TypeCons, TypeFun, Vis,
};

/// A package of all public information about a module.
///
/// Useful for resolving and canonicalizing names
pub struct Module {
    /// map from local name to type
    pub pub_data: HashMap<String, DataDecl>,
    pub pub_cons: HashMap<String, Type>,
    /// type name to tuple of generic args and actual type
    pub type_alias: HashMap<String, Type>,

    pub pub_decls: HashMap<String, QualType>,
    pub pub_gens: HashMap<String, (QualType, Vec<FunctionDef>)>,

    pub pub_typefn: HashMap<String, TypeFun>,
    pub pub_impls: HashMap<String, Vec<QualType>>,
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
            .map(|(n, (_, dd))| dd.2.iter().map(move |c| format!("{}.{}", n, c.name)))
            .flatten()
            .collect();

        let local_decls = self.typedecls.keys().cloned().collect();

        // canonicalize type aliases
        self.type_aliases = self
            .type_aliases
            .clone()
            .into_iter()
            .map(|(name, mut t)| {
                t.canonicalize(
                    prefix,
                    &local_datadecls,
                    &self.imports,
                    &self.type_aliases,
                    &self.aliases,
                );
                (format!("{prefix}/{name}"), t)
            })
            .collect();

        // canonicalize data declarations
        self.types = self
            .types
            .clone()
            .into_iter()
            .map(|(_, (is_pub, mut dd))| {
                dd.canonicalize(
                    prefix,
                    &local_datadecls,
                    &self.imports,
                    &self.type_aliases,
                    &self.aliases,
                );
                (dd.0.clone(), (is_pub, dd))
            })
            .collect();

        // canonicalize type declarations
        self.typedecls = self
            .typedecls
            .clone()
            .into_iter()
            .map(|(name, (is_pub, mut td))| {
                td.canonicalize(
                    prefix,
                    &local_datadecls,
                    &local_typefuns,
                    &self.imports,
                    &self.type_aliases,
                    &self.aliases,
                );

                let name = if self.external.contains(&name) {
                    name
                } else {
                    format!("{prefix}/{name}")
                };

                (name, (is_pub, td))
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
                        &local_datadecls,
                        &local_cons,
                        &local_typefuns,
                        &self.imports,
                        &self.aliases,
                        &self.external,
                    )
                });
                (format!("{prefix}/{name}"), funcs)
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
                    &local_datadecls,
                    &local_typefuns,
                    &self.imports,
                    &self.aliases,
                    &HashSet::new(),
                    &self.external,
                );
                (format!("{prefix}/{name}"), def)
            })
            .collect();

        // canonicalize type functions
        self.typefuns = self
            .typefuns
            .clone()
            .into_iter()
            .map(|(name, (is_pub, mut tf))| {
                tf.name = format!("{prefix}/{name}");
                tf.ty.canonicalize(
                    prefix,
                    &local_datadecls,
                    &self.imports,
                    &self.type_aliases,
                    &self.aliases,
                );

                (format!("{prefix}/{name}"), (is_pub, tf))
            })
            .collect();

        // canonicalize impls
        for impll in self.impls.iter_mut() {
            impll.canonicalize(
                prefix,
                &local_datadecls,
                &local_cons,
                &local_typefuns,
                &local_decls,
                &self.imports,
                &self.type_aliases,
                &self.aliases,
                &self.external,
            );
        }

        Module {
            pub_data: self
                .types
                .clone()
                .into_iter()
                .filter_map(|(name, (vis, ty))| {
                    if vis == Vis::Public {
                        Some((name, ty))
                    } else {
                        None
                    }
                })
                .collect(),
            pub_cons: self
                .types
                .iter()
                .filter_map(|(_, (vis, dd))| {
                    if *vis == Vis::Public {
                        Some(dd.2.iter().map(|c| (c.name.clone(), c.args.clone())))
                    } else {
                        None
                    }
                })
                .flatten()
                .collect(),
            pub_decls: self
                .typedecls
                .clone()
                .into_iter()
                .filter_map(|(name, (vis, t))| {
                    if !t.is_generic() && vis == Vis::Public {
                        Some((name, t))
                    } else {
                        None
                    }
                })
                .collect(),
            pub_gens: self
                .typedecls
                .clone()
                .into_iter()
                .filter(|(_, (vis, t))| *vis == Vis::Public && t.is_generic())
                .map(|(name, (_, t))| (name.clone(), (t, self.funcs[&name].clone())))
                .collect(),
            pub_typefn: self
                .typefuns
                .clone()
                .into_iter()
                .filter_map(|(name, (vis, tf))| {
                    if vis == Vis::Public {
                        Some((name, tf))
                    } else {
                        None
                    }
                })
                .collect(),
            pub_impls: self
                .impls
                .clone()
                .into_iter()
                .map(|i| (i.fn_name, i.args))
                .collect(),
            type_alias: self.type_aliases.clone(),
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
    //    update: it has
    pub fn resolve(&mut self, me: &str, mods: &HashMap<String, Module>) {
        // Get the names of types from other modules used in our types
        let mut imported_data = VecDeque::new();
        let mut imported_idents = VecDeque::new();

        // Basically two steps:
        // 1. aggregate all the names that we use but do not provide
        // 2. copy over the necessary data based on each name

        for (_, (_, dd)) in self.types.iter_mut() {
            dd.resolve(&mods);
            imported_data.extend(dd.imported(me));
        }

        for (_, (_, td)) in self.typedecls.iter_mut() {
            td.resolve(&mods);
            let (types, decls) = td.imported(me);
            imported_data.extend(types);
            imported_idents.extend(decls);
        }

        for (_, funcs) in self.funcs.iter() {
            for func in funcs {
                let (ts, ns) = func.imported(me);
                imported_data.extend(ts);
                imported_idents.extend(ns);
            }
        }

        for (_, defs) in self.defs.iter() {
            let (ts, ns) = defs.imported(me);
            imported_data.extend(ts);
            imported_idents.extend(ns);
        }

        for (_, TypeFun { ty, .. }) in self.typefuns.values_mut() {
            ty.resolve(mods);
            imported_data.extend(ty.imported(me));
        }

        for Impl { args, body, .. } in self.impls.iter_mut() {
            for arg in args.iter_mut() {
                arg.resolve(mods);
                let (ts, ns) = arg.imported(me);
                imported_data.extend(ts);
                imported_idents.extend(ns);
            }

            for func in body {
                let (ts, ns) = func.imported(me);
                imported_data.extend(ts);
                imported_idents.extend(ns);
            }
        }

        // Now the secret step 1.5: add the impl types and bodies
        // to the tree

        // Ensure all private typefunctions are in the private impl map
        for (vis, tf) in self.typefuns.values() {
            if *vis == Vis::Private {
                self.private_impl_map.insert(tf.name.clone(), vec![]);
            }
        }

        for Impl {
            fn_name: new_name,
            args,
            body,
            ..
        } in self.impls.clone().into_iter()
        {
            // eprintln!("{new_name:?}");
            // an impl is compiled in the module it is defined in. So, its namespace is the module
            // who created it, not the module of the typefunction
            let ns = new_name.rsplit_once("/").unwrap().0;
            let tf = new_name.rsplit_once("$").unwrap().0;

            // find the typefunction in another module, or in our own typefunctions
            let (vis, TypeFun { name, ty, vars }) = if let Some(tf) = mods[ns].pub_typefn.get(tf) {
                (Vis::Public, tf.clone())
            } else {
                self.typefuns.get(tf).unwrap().clone()
            };

            // substitutions to go from impl to real type
            let mut subs = HashMap::new();
            let mut cons = vec![];
            for (var, QualType(cs, arg)) in vars.iter().zip(args.iter()) {
                cons.extend(cs.clone());
                subs.insert(var.clone(), arg.clone());
            }

            // Get the type of the typefun
            let ty = crate::mir::typefn_type(TypeFun {
                name: name.clone(),
                ty: ty.clone(),
                vars,
            });

            let real_type = match ty.replace_all(&subs) {
                Type::ForAll(_, _, ty) => *ty,
                _ => panic!("typefun conversion failed"),
            };

            self.typedecls.insert(
                new_name.clone(),
                (vis.clone(), QualType(cons, real_type.clone())),
            );
            self.funcs.insert(new_name.clone(), body);

            // If impl visibility is private add it to the private impl map
            if vis == Vis::Private {
                self.private_impl_map
                    .get_mut(tf)
                    .unwrap()
                    .push((new_name.clone(), real_type));
            }
        }

        // Now step two:
        // imported_data is pretty simple, it will always be
        //    an alias or a declared type in its module.
        //    An alias can point to another alias, so this needs
        //    to be resolved recursively.
        // imported_idents is a littler harder, it can either
        //    be a regular function, a generic function, or
        //    a typefunction. generic functions need to be
        //    recursively resolved in a breadth first manner
        //    to account for cycles
        self.import_idents = imported_idents.clone().into_iter().collect();

        while let Some(name) = imported_data.pop_front() {
            let mod_name = name.rsplit_once("/").unwrap().0;
            let modu = &mods[mod_name];

            self.types
                .insert(name.clone(), (Vis::Import, modu.pub_data[&name].clone()));
        }

        while let Some(name) = imported_idents.pop_front() {
            let mod_name = name.rsplit_once("/").unwrap().0;
            let modu = &mods[mod_name];

            if let Some(_) = modu.pub_cons.get(&name) {
                // cons is a no op since the constructor is automatically
                // created from the data definition
            } else if let Some(decl) = modu.pub_decls.get(&name) {
                self.typedecls.insert(name, (Vis::Import, decl.clone()));
            } else if let Some(tfun) = modu.pub_typefn.get(&name) {
                self.typefuns.insert(name, (Vis::Import, tfun.clone()));
            } else if let Some((ty, body)) = modu.pub_gens.get(&name) {
                if !self.typedecls.contains_key(&name) {
                    self.typedecls
                        .insert(name.clone(), (Vis::Private, ty.clone()));

                    for f in body {
                        let (ts, ns) = f.imported(me);
                        imported_data.extend(ts);
                        imported_idents.extend(ns);
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
        type_aliases: &HashMap<String, Type>,
        aliases: &HashMap<String, String>,
    ) {
        // the name just gets hit with the prefix of this module
        self.0 = format!("{me}/{}", self.0);

        self.2
            .iter_mut()
            .for_each(|tc| tc.canonicalize(me, &self.0, types, imports, type_aliases, aliases));
    }

    fn resolve(&mut self, mods: &HashMap<String, Module>) {
        self.2.iter_mut().for_each(|tc| tc.resolve(mods));
    }

    // find all the imported types
    fn imported(&self, me: &str) -> Vec<String> {
        self.2.iter().map(|tc| tc.imported(me)).flatten().collect()
    }
}

impl TypeCons {
    fn canonicalize(
        &mut self,
        me: &str,
        tname: &str,
        types: &HashSet<String>,
        imports: &HashSet<String>,
        type_aliases: &HashMap<String, Type>,
        aliases: &HashMap<String, String>,
    ) {
        self.name = format!("{tname}.{}", self.name);
        self.args
            .canonicalize(me, types, imports, type_aliases, aliases);
    }

    fn resolve(&mut self, mods: &HashMap<String, Module>) {
        self.args.resolve(mods);
    }

    fn imported(&self, me: &str) -> Vec<String> {
        self.args.imported(me)
    }
}

impl Type {
    fn canonicalize(
        &mut self,
        me: &str,
        types: &HashSet<String>,
        imports: &HashSet<String>,
        type_aliases: &HashMap<String, Type>,
        aliases: &HashMap<String, String>,
    ) {
        // because of ownership we need to do some matching on a clone of ourself
        // only in the case of an alias
        if let Type::Ident(i) = self.clone() {
            if let Some(t) = type_aliases.get(&i) {
                *self = t.clone();
                self.canonicalize(me, types, imports, type_aliases, aliases);
            }
        }

        match self {
            Type::Ident(i) => {
                if let Some(s) = aliases.get(i) {
                    *i = s.clone();
                } else if types.contains(i) {
                    *i = format!("{me}/{}", i);
                } else if let Some((ns, _)) = i.rsplit_once("/") {
                    if !imports.contains(ns) {
                        panic!("type uses unimported ns {ns} from {i}")
                    }
                }
            }
            Type::ForAll(_, _, _) => panic!(),
            Type::Generic(ts, t) => {
                t.canonicalize(me, types, imports, type_aliases, aliases);
                ts.iter_mut()
                    .for_each(|t| t.canonicalize(me, types, imports, type_aliases, aliases));
            }
            Type::Arrow(a, b) => {
                a.canonicalize(me, types, imports, type_aliases, aliases);
                b.canonicalize(me, types, imports, type_aliases, aliases);
            }
            Type::Tuple(ts) => {
                ts.iter_mut()
                    .for_each(|t| t.canonicalize(me, types, imports, type_aliases, aliases));
            }
            _ => {}
        }
    }

    // check if a canonicalized type is generic
    fn is_generic(&self) -> bool {
        match self {
            Type::GenVar(_) => true,
            Type::ForAll(_, _, _) => panic!(),
            Type::Generic(ts, t) => ts.iter().any(|t| t.is_generic()) || t.is_generic(),
            Type::Arrow(a, b) => a.is_generic() || b.is_generic(),
            Type::Tuple(ts) => ts.iter().any(|t| t.is_generic()),
            _ => false,
        }
    }

    fn resolve(&mut self, mods: &HashMap<String, Module>) {
        match self {
            Type::Ident(i) => {
                if let Some((ns, _)) = i.rsplit_once("/") {
                    if let Some(t) = mods[ns].type_alias.get(i) {
                        *self = t.clone();
                    }
                }
            }
            Type::ForAll(_, _, _) => panic!("{self:?}"),
            Type::Generic(ts, t) => {
                ts.iter_mut().for_each(|t| t.resolve(mods));
                t.resolve(mods);
            }
            Type::Arrow(a, b) => {
                a.resolve(mods);
                b.resolve(mods);
            }
            Type::Tuple(ts) => ts.iter_mut().for_each(|t| t.resolve(mods)),
            _ => {}
        }
    }

    fn imported(&self, me: &str) -> Vec<String> {
        match self {
            Type::Ident(i) if i.contains("/") && !i.starts_with(me) => {
                vec![i.clone()]
            }
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
        type_aliases: &HashMap<String, Type>,
        aliases: &HashMap<String, String>,
    ) {
        let QualType(cons, t) = self;

        cons.iter_mut()
            .for_each(|c| c.canonicalize(me, types, typefuns, imports, type_aliases, aliases));
        t.canonicalize(me, types, imports, type_aliases, aliases);
    }

    // Check if a canonicalized QualType has generic params
    fn is_generic(&self) -> bool {
        self.1.is_generic()
    }

    fn resolve(&mut self, mods: &HashMap<String, Module>) {
        self.1.resolve(mods);
    }

    fn imported(&self, me: &str) -> (Vec<String>, Vec<String>) {
        let mut types = vec![];
        let mut decls = vec![];

        self.0.iter().for_each(|c| {
            let (t, d) = c.imported(me);
            types.extend(t);
            decls.extend(d);
        });
        types.extend(self.1.imported(me));
        (types, decls)
    }
}

impl Constraint {
    fn canonicalize(
        &mut self,
        me: &str,
        types: &HashSet<String>,
        typefuns: &HashSet<String>,
        imports: &HashSet<String>,
        type_aliases: &HashMap<String, Type>,
        aliases: &HashMap<String, String>,
    ) {
        let Constraint(name, ts) = self;

        if typefuns.contains(name) {
            *name = format!("{me}/{name}");
        } else if let Some((ns, _)) = name.rsplit_once("/") {
            if !imports.contains(ns) {
                panic!()
            }
        } else {
            panic!("can't find constraint")
        }

        ts.iter_mut()
            .for_each(|t| t.canonicalize(me, types, imports, type_aliases, aliases));
    }

    fn imported(&self, me: &str) -> (Vec<String>, Vec<String>) {
        let types = self.1.iter().map(|t| t.imported(me)).flatten().collect();
        let decls = if self.0.contains("/") && !self.0.starts_with(me) {
            vec![self.0.clone()]
        } else {
            vec![]
        };

        (types, decls)
    }
}

impl Impl {
    fn canonicalize(
        &mut self,
        me: &str,
        types: &HashSet<String>,
        cons: &HashSet<String>,
        typefuns: &HashSet<String>,
        decls: &HashSet<String>,
        imports: &HashSet<String>,
        type_aliases: &HashMap<String, Type>,
        aliases: &HashMap<String, String>,
        external: &HashSet<String>,
    ) {
        // Every impl gets a unique global name based on their typefunction name.
        // eprintln!("{me} {} {:?}", self.fn_name, aliases);
        let name = aliases.get(&self.fn_name).unwrap_or(&self.fn_name);
        self.fn_name = crate::gen_var(&if typefuns.contains(name) {
            format!("{me}/{}$", name)
        } else {
            format!("{}$", name)
        });

        self.args
            .iter_mut()
            .for_each(|t| t.canonicalize(me, types, typefuns, imports, type_aliases, aliases));

        self.body.iter_mut().for_each(|fd| {
            fd.canonicalize(me, decls, types, cons, typefuns, imports, aliases, external)
        });
    }
}

impl FunctionDef {
    fn canonicalize(
        &mut self,
        me: &str,
        decls: &HashSet<String>,
        types: &HashSet<String>,
        cons: &HashSet<String>,
        typefuns: &HashSet<String>,
        imports: &HashSet<String>,
        aliases: &HashMap<String, String>,
        external: &HashSet<String>,
    ) {
        self.name = format!("{me}/{}", self.name);

        self.args.canonicalize(me, types, aliases, imports);
        let mut locals = HashSet::new();
        locals.extend(self.args.free_vars());

        self.body.canonicalize(
            me, decls, cons, types, typefuns, imports, aliases, &locals, external,
        );
    }

    fn imported(&self, me: &str) -> (Vec<String>, Vec<String>) {
        let mut ts = self.args.imported(me);
        let (a, ns) = self.body.imported(me);
        ts.extend(a);
        (ts, ns)
    }
}

impl Pattern {
    fn canonicalize(
        &mut self,
        me: &str,
        types: &HashSet<String>,
        aliases: &HashMap<String, String>,
        imports: &HashSet<String>,
    ) {
        match self {
            Pattern::Cons(f, args, _) => {
                let fc = f.clone();
                let (t, c) = fc.rsplit_once(".").unwrap();

                let ty = match aliases.get(t) {
                    Some(s) => s,
                    _ => t,
                };

                *f = format!("{ty}.{c}");

                if types.contains(ty) {
                    *f = format!("{me}/{ty}.{c}");
                } else if let Some((ns, _)) = ty.rsplit_once("/") {
                    if !imports.contains(ns) {
                        panic!("where does {ty}.{c} come from?");
                    }
                } else {
                    panic!("cons pattern not in module or imports {ty}.{c}")
                }

                args.canonicalize(me, types, aliases, imports);
            }
            Pattern::Tuple(ps, _) => {
                ps.iter_mut()
                    .for_each(|p| p.canonicalize(me, types, aliases, imports));
            }
            _ => {}
        }
    }

    fn imported(&self, me: &str) -> Vec<String> {
        match self {
            Pattern::Cons(f, args, _) => {
                let mut rest = args.imported(me);

                if !f.starts_with(me) {
                    let (ty, _) = f.rsplit_once(".").unwrap();
                    rest.push(ty.to_string());
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
        types: &HashSet<String>,
        typefuns: &HashSet<String>,
        imports: &HashSet<String>,
        aliases: &HashMap<String, String>,
        locals: &HashSet<String>,
        external: &HashSet<String>,
    ) {
        // First apply aliases to identifier
        if let Expression::Identifier(i) = self {
            if let Some(v) = aliases.get(i) {
                // if i is an alias expand it
                *i = v.clone();
            } else if let Some((t, c)) = i.clone().rsplit_once(".") {
                // If i is a call to a cons where the type is an
                // alias then expand it
                if let Some(v) = aliases.get(t) {
                    *i = format!("{v}.{c}");
                }
            }
        }

        match self {
            Expression::Identifier(i) => {
                if external.contains(i) {
                    // do nothing, you are perfect just the way you are
                } else if decls.contains(i) || cons.contains(i) || typefuns.contains(i) {
                    *i = format!("{me}/{i}");
                } else if let Some((ns, _)) = i.clone().rsplit_once("/") {
                    if !imports.contains(ns) {
                        panic!("namespace {ns} not imported")
                    }
                } else if !locals.contains(i) {
                    if i != "llvm!" {
                        panic!("undeclared variable {i}");
                    }
                }
            }
            Expression::Let(p, e, body) => {
                p.canonicalize(me, types, aliases, imports);
                e.canonicalize(
                    me, decls, cons, types, typefuns, imports, aliases, locals, external,
                );

                let mut locals = locals.clone();
                locals.extend(p.free_vars());
                body.canonicalize(
                    me, decls, cons, types, typefuns, imports, aliases, &locals, external,
                );
            }
            Expression::Tuple(es) => {
                es.iter_mut().for_each(|e| {
                    e.canonicalize(
                        me, decls, cons, types, typefuns, imports, aliases, locals, external,
                    )
                });
            }
            Expression::If(cond, a, b) => {
                cond.canonicalize(
                    me, decls, cons, types, typefuns, imports, aliases, locals, external,
                );
                a.canonicalize(
                    me, decls, cons, types, typefuns, imports, aliases, locals, external,
                );
                b.canonicalize(
                    me, decls, cons, types, typefuns, imports, aliases, locals, external,
                );
            }
            Expression::Match(e, eps) => {
                e.canonicalize(
                    me, decls, cons, types, typefuns, imports, aliases, locals, external,
                );

                for (p, e) in eps {
                    p.canonicalize(me, types, aliases, imports);

                    let mut locals = locals.clone();
                    locals.extend(p.free_vars());
                    e.canonicalize(
                        me, decls, cons, types, typefuns, imports, aliases, &locals, external,
                    );
                }
            }
            Expression::Call(a, b) => {
                a.canonicalize(
                    me, decls, cons, types, typefuns, imports, aliases, locals, external,
                );
                b.canonicalize(
                    me, decls, cons, types, typefuns, imports, aliases, locals, external,
                );
            }
            Expression::Lambda(p, e) => {
                p.canonicalize(me, types, aliases, imports);

                let mut locals = locals.clone();
                locals.extend(p.free_vars());
                e.canonicalize(
                    me, decls, cons, types, typefuns, imports, aliases, &locals, external,
                );
            }
            _ => {}
        }
    }

    fn imported(&self, me: &str) -> (Vec<String>, Vec<String>) {
        let mut ts = vec![];
        let mut ns = vec![];

        match self {
            Expression::Identifier(i) => {
                if i.contains("/") && !i.starts_with(me) {
                    ns.push(i.clone());

                    if let Some((t, _)) = i.rsplit_once(".") {
                        ts.push(t.to_string());
                    }
                }
            }
            Expression::Let(p, e, body) => {
                ts.extend(p.imported(me));

                let (a, b) = e.imported(me);
                ts.extend(a);
                ns.extend(b);

                let (a, b) = body.imported(me);
                ts.extend(a);
                ns.extend(b);
            }
            Expression::Tuple(es) => {
                for e in es {
                    let (a, b) = e.imported(me);
                    ts.extend(a);
                    ns.extend(b);
                }
            }
            Expression::If(cond, y, n) => {
                let (a, b) = cond.imported(me);
                ts.extend(a);
                ns.extend(b);

                let (a, b) = y.imported(me);
                ts.extend(a);
                ns.extend(b);

                let (a, b) = n.imported(me);
                ts.extend(a);
                ns.extend(b);
            }
            Expression::Match(e, eps) => {
                let (a, b) = e.imported(me);
                ts.extend(a);
                ns.extend(b);

                for (p, e) in eps {
                    ts.extend(p.imported(me));
                    let (a, b) = e.imported(me);
                    ts.extend(a);
                    ns.extend(b);
                }
            }
            Expression::Call(m, n) => {
                let (a, b) = m.imported(me);
                ts.extend(a);
                ns.extend(b);

                let (a, b) = n.imported(me);
                ts.extend(a);
                ns.extend(b);
            }
            Expression::Lambda(p, e) => {
                ts.extend(p.imported(me));
                let (a, b) = e.imported(me);

                ts.extend(a);
                ns.extend(b);
            }
            _ => {}
        }

        (ts, ns)
    }
}
