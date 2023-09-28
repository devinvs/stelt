use std::collections::HashMap;
use std::collections::HashSet;

use crate::lexer::Lexeme;
use crate::lexer::LexemeFeed;
use crate::lexer::Lexer;
use crate::lexer::TokenStream;
use crate::Token;

use crate::parse_tree::{
    DataDecl, Expression, FunctionDef, Impl, ParseTree, Pattern, Type, TypeCons, TypeFun,
};

use lazy_static::lazy_static;

lazy_static! {
    static ref PRELUDE: ParseTree = {
        let s = include_str!("./prelude.st");
        let mut l = Lexer::default();
        let mut tokens = l.lex(s).unwrap();

        let me = ParseTree {
            types: Vec::new(),
            typedefs: HashMap::new(),
            funcs: HashMap::new(),
            defs: HashMap::new(),
            external: HashSet::new(),
            namespaces: HashSet::new(),
            imports: HashSet::new(),
            import_funcs: HashMap::new(),
            typefuns: HashMap::new(),
            impls: Vec::new(),
        };
        ParseTree::parse_with(&mut tokens, me).unwrap()
        // me
    };
}

fn prefixed(pref: &str, n: &str) -> String {
    if pref == "" {
        n.to_string()
    } else {
        format!("{pref}.{n}")
    }
}

impl ParseTree {
    pub fn parse(t: &mut TokenStream) -> Result<Self, String> {
        Self::parse_with(t, PRELUDE.clone())
    }

    pub fn parse_with(t: &mut TokenStream, mut me: Self) -> Result<Self, String> {
        loop {
            match t.peek() {
                Some(Lexeme { token: Token::Impl }) => {
                    t.assert(Token::Impl)?;
                    let name = t.ident()?;

                    let mut gen_args = vec![];
                    if t.consume(Token::LArrow).is_some() {
                        loop {
                            let i = t.ident()?;
                            gen_args.push(i);
                            if t.consume(Token::Comma).is_none() {
                                break;
                            }
                        }

                        t.assert(Token::RArrow)?;
                    }

                    let mut args = vec![];
                    t.assert(Token::LParen)?;
                    while let Ok(ty) = Type::parse(t) {
                        args.push(ty);
                        if t.consume(Token::Comma).is_none() {
                            break;
                        }
                    }
                    t.assert(Token::RParen)?;

                    let mut funcs = vec![];
                    while t.peek()
                        == Some(&Lexeme {
                            token: Token::Ident(name.clone()),
                        })
                    {
                        let name = t.ident()?;
                        let func = FunctionDef::parse(t, name, &me.namespaces)?;
                        funcs.push(func);
                    }

                    me.impls.push(Impl {
                        fn_name: name,
                        gen_args,
                        args,
                        body: funcs,
                    });
                }
                Some(Lexeme {
                    token: Token::Typefn,
                }) => {
                    t.assert(Token::Typefn)?;

                    let name = t.ident()?;
                    let mut gen_args = vec![];
                    if t.consume(Token::LArrow).is_some() {
                        while let Ok(id) = t.ident() {
                            gen_args.push(id);
                            if t.consume(Token::Comma).is_none() {
                                break;
                            }
                        }
                        t.assert(Token::RArrow)?;
                    }

                    let mut args = vec![];
                    t.assert(Token::LParen)?;
                    while let Ok(id) = t.ident() {
                        args.push(id);
                        if t.consume(Token::Comma).is_none() {
                            break;
                        }
                    }

                    t.assert(Token::RParen)?;
                    t.assert(Token::Assign)?;
                    let ty = Type::parse(t)?;

                    me.typefuns.insert(
                        name.clone(),
                        TypeFun {
                            name,
                            vars: args,
                            ty: Type::ForAll(gen_args, Box::new(ty)),
                        },
                    );
                }
                Some(Lexeme {
                    token: Token::Import,
                }) => {
                    t.assert(Token::Import)?;
                    let mut namespace = t.ident()?;
                    while t.consume(Token::Dot).is_some() {
                        namespace.push_str(".");
                        namespace.push_str(&t.ident()?);
                    }

                    me.namespaces.insert(namespace);
                }
                Some(Lexeme {
                    token: Token::Extern,
                    ..
                }) => {
                    t.assert(Token::Extern)?;
                    // must be a typedecl
                    t.assert(Token::Type)?;

                    let name = t.ident()?;
                    t.assert(Token::Colon)?;

                    let ty = Type::parse(t)?;
                    me.typedefs.insert(name.clone(), ty);
                    me.external.insert(name);
                }
                Some(Lexeme {
                    token: Token::Type, ..
                }) => {
                    // Either a typedecl or datadecl
                    t.assert(Token::Type)?;

                    let name = t.ident()?;

                    // generic args for forall type
                    let mut args = Vec::new();
                    if t.consume(Token::LArrow).is_some() {
                        let arg = t.ident()?;
                        args.push(arg);

                        while t.consume(Token::Comma).is_some() {
                            let arg = t.ident()?;
                            args.push(arg);
                        }

                        t.assert(Token::RArrow)?;
                    }

                    match t.next() {
                        Some(Lexeme {
                            token: Token::Assign,
                            ..
                        }) => {
                            let ty = DataDecl::parse(t, name.clone(), args)?;
                            me.types.push((name, ty));
                        }
                        Some(Lexeme {
                            token: Token::Colon,
                            ..
                        }) => {
                            let ty = Type::parse(t)?;
                            me.typedefs.insert(name, Type::ForAll(args, Box::new(ty)));
                        }
                        Some(a) => {
                            return Err(format!(
                                "Expected colon or equals, found '{}'",
                                a.token.name()
                            ))
                        }
                        None => return Err(format!("Expected colon or equals, found EOF")),
                    }
                }
                Some(Lexeme {
                    token: Token::Def, ..
                }) => {
                    let name = t.ident()?;

                    let expr = Expression::parse(t)?.extract_ns(&me.namespaces);
                    me.defs.insert(name, expr);
                }
                Some(Lexeme {
                    token: Token::Ident(_),
                    ..
                }) => {
                    let name = t.ident()?;
                    let func = FunctionDef::parse(t, name, &me.namespaces)?;
                    if let Some(f) = me.funcs.get_mut(&func.name) {
                        f.push(func);
                    } else {
                        me.funcs.insert(func.name.clone(), vec![func]);
                    }
                }
                Some(a) => return Err(format!("Unexpected token in declaration: '{:?}'", a.token)),
                None => break,
            }
        }

        Ok(me)
    }

    /// Resolve all namespace references
    ///
    /// Type references are copied into our tree
    /// Functions and defs have their type decls copied
    /// Generic functions have their bodies copied into our tree
    ///
    /// Finally we prefix our own types with our own module name
    pub fn resolve(self, mods: &HashMap<String, Self>, mod_name: &str) -> Self {
        let mut ref_types = HashMap::new();
        let mut type_decls = HashMap::new();

        let mut typedefs: HashMap<String, Type> = self
            .typedefs
            .iter()
            .map(|(name, td)| {
                (
                    if self.external.contains(name) {
                        name.clone()
                    } else {
                        prefixed(mod_name, name)
                    },
                    td.clone()
                        .resolve(&mut ref_types, mods)
                        .qualify(mod_name, &self),
                )
            })
            .collect();

        let mut types: Vec<(String, DataDecl)> = self
            .types
            .iter()
            .map(|(name, data)| {
                (
                    prefixed(mod_name, name),
                    data.clone()
                        .resolve(&mut ref_types, mods)
                        .qualify(mod_name, &self),
                )
            })
            .collect();

        let mut generics = HashMap::new();
        let mut funcs: HashMap<String, Vec<FunctionDef>> = self
            .funcs
            .iter()
            .map(|(name, fs)| {
                (
                    prefixed(mod_name, name),
                    fs.into_iter()
                        .map(|f| {
                            f.clone()
                                .resolve(&mut ref_types, &mut type_decls, &mut generics, mods)
                                .qualify(mod_name, &self)
                        })
                        .collect(),
                )
            })
            .collect();

        let defs: HashMap<String, Expression> = self
            .defs
            .iter()
            .map(|(name, d)| {
                (
                    prefixed(mod_name, name),
                    d.clone()
                        .resolve(&mut ref_types, &mut type_decls, &mut generics, mods)
                        .qualify(mod_name, &self),
                )
            })
            .collect();

        let mut imports = HashSet::new();
        imports.extend(ref_types.clone().into_keys());
        imports.extend(generics.clone().into_keys());
        imports.extend(type_decls.clone().into_keys());

        types.extend(ref_types);
        typedefs.extend(type_decls.clone());
        funcs.extend(generics);

        Self {
            types,
            external: self.external,
            typedefs,
            funcs,
            defs,
            namespaces: self.namespaces,
            imports,
            import_funcs: type_decls,

            // TODO: fix later
            impls: self.impls,
            typefuns: self.typefuns,
        }
    }
}

impl DataDecl {
    fn qualify(self, prefix: &str, me: &ParseTree) -> Self {
        let DataDecl(name, args, cons) = self;
        DataDecl(
            name,
            args,
            cons.into_iter()
                .map(|cons| cons.qualify(prefix, me))
                .collect(),
        )
    }

    fn has_cons(&self, name: &str) -> bool {
        let DataDecl(_, _, cons) = self;
        cons.iter().any(|c| c.name == name)
    }

    fn resolve(
        self,
        rt: &mut HashMap<String, DataDecl>,
        mods: &HashMap<String, ParseTree>,
    ) -> Self {
        let DataDecl(name, args, cons) = self;
        DataDecl(
            name,
            args,
            cons.into_iter().map(|c| c.resolve(rt, mods)).collect(),
        )
    }

    fn parse(t: &mut TokenStream, name: String, args: Vec<String>) -> Result<Self, String> {
        let mut cons = Vec::new();
        let con = TypeCons::parse(t)?;
        cons.push(con);

        while t.consume(Token::Bar).is_some() {
            let con = TypeCons::parse(t)?;
            cons.push(con);
        }

        Ok(Self(name, args, cons))
    }
}

impl TypeCons {
    fn qualify(self, prefix: &str, me: &ParseTree) -> Self {
        Self {
            name: prefixed(prefix, &self.name),
            args: self.args.qualify(prefix, me),
        }
    }

    fn resolve(
        self,
        rt: &mut HashMap<String, DataDecl>,
        mods: &HashMap<String, ParseTree>,
    ) -> Self {
        Self {
            name: self.name,
            args: self.args.resolve(rt, mods),
        }
    }

    fn parse(t: &mut TokenStream) -> Result<Self, String> {
        let name = t.ident()?;

        let args = if t.test(Token::LParen) {
            Type::parse(t)?
        } else {
            Type::Unit
        };

        Ok(Self { name, args })
    }
}

impl FunctionDef {
    fn qualify(self, prefix: &str, me: &ParseTree) -> Self {
        Self {
            name: self.name,
            args: self.args.qualify(prefix, me),
            body: self.body.qualify(prefix, me),
        }
    }

    fn resolve(
        self,
        rt: &mut HashMap<String, DataDecl>,
        td: &mut HashMap<String, Type>,
        g: &mut HashMap<String, Vec<FunctionDef>>,
        mods: &HashMap<String, ParseTree>,
    ) -> Self {
        Self {
            name: self.name,
            args: self.args.resolve(rt, mods),
            body: self.body.resolve(rt, td, g, mods),
        }
    }

    fn parse(t: &mut TokenStream, name: String, ns: &HashSet<String>) -> Result<Self, String> {
        // Force function def to start with open paren, but don't consume
        if !t.test(Token::LParen) {
            // Guaranteed to error
            t.assert(Token::LParen)?;
        }

        let args = Pattern::parse(t)?;

        t.assert(Token::Assign)?;

        let mut body = Expression::parse(t)?.extract_ns(ns);

        if t.consume(Token::Where).is_some() {
            let p = Pattern::parse(t)?;
            t.assert(Token::Assign)?;
            let e = Expression::parse(t)?;

            let mut bindings = vec![(p, e)];

            while t.consume(Token::Bar).is_some() {
                let p = Pattern::parse(t)?;
                t.assert(Token::Assign)?;
                let e = Expression::parse(t)?;
                bindings.push((p, e));
            }
            bindings.reverse();

            for (p, e) in bindings {
                body = Expression::Let(p, Box::new(e), Box::new(body));
            }
        }

        return Ok(FunctionDef { name, args, body });
    }
}

impl Type {
    fn qualify(self, prefix: &str, me: &ParseTree) -> Self {
        match self {
            Type::Ident(t) => {
                if me.types.iter().any(|(a, _)| *a == t) {
                    Type::Ident(prefixed(prefix, &t))
                } else {
                    Type::Ident(t)
                }
            }
            Type::ForAll(args, t) => Type::ForAll(args, Box::new(t.qualify(prefix, me))),
            Type::Generic(ts, t) => Type::Generic(
                ts.into_iter().map(|t| t.qualify(prefix, me)).collect(),
                Box::new(t.qualify(prefix, me)),
            ),
            Type::Arrow(a, b) => Type::Arrow(
                Box::new(a.qualify(prefix, me)),
                Box::new(b.qualify(prefix, me)),
            ),
            Type::Tuple(ts) => Type::Tuple(ts.into_iter().map(|t| t.qualify(prefix, me)).collect()),
            Type::Box(t) => Type::Box(Box::new(t.qualify(prefix, me))),
            a => a,
        }
    }

    fn resolve(
        self,
        ref_types: &mut HashMap<String, DataDecl>,
        mods: &HashMap<String, ParseTree>,
    ) -> Self {
        match self {
            Self::Namespace(ns, t) => {
                let ref_type = mods[&ns]
                    .types
                    .iter()
                    .find(|(n, _)| *n == t)
                    .map(|(_, ty)| ty.clone())
                    .unwrap();

                // the ref_type can contain other referenced types from other modules,
                // so we must resolve those first
                let mut other_types = HashMap::new();
                let ref_type = ref_type
                    .resolve(&mut other_types, mods)
                    .qualify(&ns, &mods[&ns]);

                ref_types.insert(format!("{ns}.{t}"), ref_type);
                ref_types.extend(other_types);

                Self::Ident(format!("{ns}.{t}"))
            }
            Self::ForAll(vars, t) => Self::ForAll(vars, Box::new(t.resolve(ref_types, mods))),
            Self::Generic(ts, t) => Self::Generic(
                ts.into_iter().map(|t| t.resolve(ref_types, mods)).collect(),
                Box::new(t.resolve(ref_types, mods)),
            ),
            Self::Arrow(a, b) => Self::Arrow(
                Box::new(a.resolve(ref_types, mods)),
                Box::new(b.resolve(ref_types, mods)),
            ),
            Self::Tuple(ts) => {
                Self::Tuple(ts.into_iter().map(|t| t.resolve(ref_types, mods)).collect())
            }
            Self::Box(t) => Self::Box(Box::new(t.resolve(ref_types, mods))),
            a => a,
        }
    }

    pub fn from_str(s: &str) -> Result<Self, String> {
        let mut l = Lexer::default();
        let mut tokens = l.lex(s)?;
        Type::parse(&mut tokens)
    }

    fn parse(t: &mut TokenStream) -> Result<Self, String> {
        let cont = Self::parse_tuple(t)?;

        if t.consume(Token::Arrow).is_some() {
            let end = Self::parse_tuple(t)?;

            Ok(Self::Arrow(Box::new(cont), Box::new(end)))
        } else {
            Ok(cont)
        }
    }

    fn parse_tuple(t: &mut TokenStream) -> Result<Self, String> {
        if t.consume(Token::LParen).is_some() {
            if t.consume(Token::RParen).is_some() {
                // Not a tuple, an empty type
                return Ok(Self::Unit);
            }

            let mut inner = vec![Self::parse(t)?];

            // Parse comma separated fields
            while t.consume(Token::Comma).is_some() {
                inner.push(Self::parse(t)?);
            }

            t.assert(Token::RParen)?;

            if inner.len() == 1 {
                Ok(inner.pop().unwrap())
            } else {
                Ok(Self::Tuple(inner))
            }
        } else {
            Ok(Self::parse_list(t)?)
        }
    }

    fn parse_list(t: &mut TokenStream) -> Result<Self, String> {
        if t.consume(Token::LBrace).is_some() {
            let inner = Self::parse(t)?;

            t.assert(Token::RBrace)?;

            Ok(Self::Generic(
                vec![inner],
                Box::new(Self::Ident("list".to_string())),
            ))
        } else {
            Self::parse_generic(t)
        }
    }

    fn parse_generic(t: &mut TokenStream) -> Result<Self, String> {
        let base = Self::parse_base(t)?;

        if t.consume(Token::LArrow).is_some() {
            let mut vars = Vec::new();
            vars.push(Self::parse(t)?);

            while t.consume(Token::Comma).is_some() {
                vars.push(Self::parse(t)?);
            }

            t.assert(Token::RArrow)?;

            Ok(Self::Generic(vars, Box::new(base)))
        } else if t.consume(Token::Question).is_some() {
            Ok(Self::Generic(
                vec![base],
                Box::new(Self::Ident("maybe".into())),
            ))
        } else {
            Ok(base)
        }
    }

    fn parse_base(t: &mut TokenStream) -> Result<Self, String> {
        Ok(match t.next() {
            Some(Lexeme {
                token: Token::Ident(mut i),
                ..
            }) => {
                while t.consume(Token::Dot).is_some() {
                    i.push_str(".");
                    i.push_str(&t.ident()?);
                }

                if let Some((ns, t)) = i.rsplit_once(".") {
                    Type::Namespace(ns.to_string(), t.to_string())
                } else {
                    Type::Ident(i)
                }
            }
            Some(Lexeme {
                token: Token::U8, ..
            }) => Self::U8,
            Some(Lexeme {
                token: Token::U16, ..
            }) => Self::U16,
            Some(Lexeme {
                token: Token::U32, ..
            }) => Self::U32,
            Some(Lexeme {
                token: Token::U64, ..
            }) => Self::U64,
            Some(Lexeme {
                token: Token::I8, ..
            }) => Self::I8,
            Some(Lexeme {
                token: Token::I16, ..
            }) => Self::I16,
            Some(Lexeme {
                token: Token::I32, ..
            }) => Self::I32,
            Some(Lexeme {
                token: Token::I64, ..
            }) => Self::I64,
            Some(a) => return Err(format!("Unexpected token in type: '{}'", a.token.name())),
            None => return Err(format!("Unexpected EOF in type")),
        })
    }
}

impl Expression {
    // Convert global identifiers to fully qualified name
    fn qualify(self, prefix: &str, me: &ParseTree) -> Self {
        match self {
            Self::Identifier(i) => {
                if me.external.contains(&i) {
                    Self::Identifier(i)
                } else if me.typedefs.contains_key(&i) {
                    Expression::Identifier(prefixed(prefix, &i))
                } else if me
                    .types
                    .iter()
                    .map(|(_, a)| a)
                    .any(|data| data.has_cons(&i))
                {
                    Expression::Identifier(prefixed(prefix, &i))
                } else {
                    Self::Identifier(i)
                }
            }
            Expression::Tuple(es) => {
                Expression::Tuple(es.into_iter().map(|e| e.qualify(prefix, me)).collect())
            }
            Expression::ExprList(es) => {
                Expression::ExprList(es.into_iter().map(|e| e.qualify(prefix, me)).collect())
            }
            Expression::Let(p, x, n) => Expression::Let(
                p.qualify(prefix, me),
                Box::new(x.qualify(prefix, me)),
                Box::new(n.qualify(prefix, me)),
            ),
            Expression::If(c, a, b) => Expression::If(
                Box::new(c.qualify(prefix, me)),
                Box::new(a.qualify(prefix, me)),
                Box::new(b.qualify(prefix, me)),
            ),
            Expression::Match(e, ps) => Expression::Match(
                Box::new(e.qualify(prefix, me)),
                ps.into_iter()
                    .map(|(p, e)| (p.qualify(prefix, me), e.qualify(prefix, me)))
                    .collect(),
            ),
            Expression::Call(m, n) => Expression::Call(
                Box::new(m.qualify(prefix, me)),
                Box::new(n.qualify(prefix, me)),
            ),
            Expression::Lambda(x, n) => {
                Expression::Lambda(x.qualify(prefix, me), Box::new(n.qualify(prefix, me)))
            }
            a => a,
        }
    }

    fn resolve(
        self,
        rt: &mut HashMap<String, DataDecl>,
        td: &mut HashMap<String, Type>,
        g: &mut HashMap<String, Vec<FunctionDef>>,
        mods: &HashMap<String, ParseTree>,
    ) -> Self {
        match self {
            Expression::Namespace(ns, n) => {
                if let Some(t) = mods[&ns].typedefs.get(&n) {
                    // this is a function/def with a declared tye
                    let t = t.clone().resolve(rt, mods).qualify(&ns, &mods[&ns]);

                    let t = if let Type::ForAll(args, t) = t {
                        if args.len() > 0 {
                            let f = mods[&ns].funcs[&n].clone();
                            // resolve references inside of f
                            let f = f
                                .into_iter()
                                .map(|fd| fd.resolve(rt, td, g, mods))
                                .map(|fd| fd.qualify(&ns, &mods[&ns]))
                                .collect();

                            g.insert(format!("{ns}.{n}"), f);
                            Box::new(Type::ForAll(args, t))
                        } else {
                            t
                        }
                    } else {
                        Box::new(t)
                    };

                    td.insert(format!("{ns}.{n}"), *t.clone());
                } else {
                    // This is a type cons
                    let t = mods[&ns]
                        .types
                        .iter()
                        .find(|(_, t)| t.has_cons(&n))
                        .unwrap();
                    let newt = t.1.clone().resolve(rt, mods).qualify(&ns, &mods[&ns]);
                    rt.insert(format!("{ns}.{}", t.0), newt);
                }

                Expression::Identifier(format!("{ns}.{n}"))
            }
            Expression::Tuple(es) => {
                Expression::Tuple(es.into_iter().map(|e| e.resolve(rt, td, g, mods)).collect())
            }
            Expression::ExprList(es) => {
                Expression::ExprList(es.into_iter().map(|e| e.resolve(rt, td, g, mods)).collect())
            }
            Expression::Let(p, x, n) => Expression::Let(
                p.resolve(rt, mods),
                Box::new(x.resolve(rt, td, g, mods)),
                Box::new(n.resolve(rt, td, g, mods)),
            ),
            Expression::If(c, a, b) => Expression::If(
                Box::new(c.resolve(rt, td, g, mods)),
                Box::new(a.resolve(rt, td, g, mods)),
                Box::new(b.resolve(rt, td, g, mods)),
            ),
            Expression::Match(e, ps) => Expression::Match(
                Box::new(e.resolve(rt, td, g, mods)),
                ps.into_iter()
                    .map(|(p, e)| (p.resolve(rt, mods), e.resolve(rt, td, g, mods)))
                    .collect(),
            ),
            Expression::Call(m, n) => Expression::Call(
                Box::new(m.resolve(rt, td, g, mods)),
                Box::new(n.resolve(rt, td, g, mods)),
            ),
            Expression::Lambda(x, n) => {
                Expression::Lambda(x.resolve(rt, mods), Box::new(n.resolve(rt, td, g, mods)))
            }
            a => a,
        }
    }

    fn extract_ns(self, ns: &HashSet<String>) -> Self {
        match self {
            Expression::Tuple(es) => {
                Expression::Tuple(es.into_iter().map(|e| e.extract_ns(ns)).collect())
            }
            Expression::ExprList(es) => {
                Expression::ExprList(es.into_iter().map(|e| e.extract_ns(ns)).collect())
            }
            Expression::Let(p, x, then) => {
                Expression::Let(p, Box::new(x.extract_ns(ns)), Box::new(then.extract_ns(ns)))
            }
            Expression::If(c, a, b) => Expression::If(
                Box::new(c.extract_ns(ns)),
                Box::new(a.extract_ns(ns)),
                Box::new(b.extract_ns(ns)),
            ),
            Expression::Match(e, ps) => Expression::Match(
                Box::new(e.extract_ns(ns)),
                ps.into_iter().map(|(p, e)| (p, e.extract_ns(ns))).collect(),
            ),
            Expression::Call(m, n) => {
                Expression::Call(Box::new(m.extract_ns(ns)), Box::new(n.extract_ns(ns)))
            }
            Expression::Lambda(x, m) => Expression::Lambda(x, Box::new(m.extract_ns(ns))),
            a => a,
        }
    }

    // general parsing strategy for expressions:
    // - start with all the left recursive operators
    // - which fall through to the right recursive operators
    // - which call the base expressions
    //    + base is a little misleading, this includes
    //      ifelse, letin, etc
    //    + anything that has an unambiguous delimiting tokens
    pub fn parse(t: &mut TokenStream) -> Result<Self, String> {
        let and = Self::andexpr(t)?;

        if let Some(()) = t.consume(Token::Or) {
            let end = Self::orexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("or".into())),
                Box::new(Self::Tuple(vec![and, end])),
            ))
        } else {
            Ok(and)
        }
    }

    pub fn orexpr(t: &mut TokenStream) -> Result<Self, String> {
        let and = Self::andexpr(t)?;

        if let Some(()) = t.consume(Token::Or) {
            let end = Self::orexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("or".into())),
                Box::new(Self::Tuple(vec![and, end])),
            ))
        } else {
            Ok(and)
        }
    }

    fn andexpr(t: &mut TokenStream) -> Result<Self, String> {
        let bitor = Self::bitorexpr(t)?;

        if let Some(()) = t.consume(Token::And) {
            let end = Self::andexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("and".into())),
                Box::new(Self::Tuple(vec![bitor, end])),
            ))
        } else {
            Ok(bitor)
        }
    }

    fn bitorexpr(t: &mut TokenStream) -> Result<Self, String> {
        let xor = Self::bitxorexpr(t)?;
        Ok(xor)

        // if let Some(()) = t.consume(Token::Bar) {
        //     let end = Self::bitorexpr(t)?;
        //     Ok(Self::Call(
        //         Box::new(Self::Identifier("bitor".into())),
        //         Box::new(Self::Tuple(vec![xor, end])),
        //     ))
        // } else {
        //     Ok(xor)
        // }
    }

    fn bitxorexpr(t: &mut TokenStream) -> Result<Self, String> {
        let and = Self::bitandexpr(t)?;

        if let Some(()) = t.consume(Token::BitXor) {
            let end = Self::bitxorexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("bitxor".into())),
                Box::new(Self::Tuple(vec![and, end])),
            ))
        } else {
            Ok(and)
        }
    }

    fn bitandexpr(t: &mut TokenStream) -> Result<Self, String> {
        let eq = Self::eqexpr(t)?;

        if let Some(()) = t.consume(Token::BitAnd) {
            let end = Self::bitandexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("bitand".into())),
                Box::new(Self::Tuple(vec![eq, end])),
            ))
        } else {
            Ok(eq)
        }
    }

    fn eqexpr(t: &mut TokenStream) -> Result<Self, String> {
        let rel = Self::relexpr(t)?;

        if let Some(()) = t.consume(Token::NotEqual) {
            let end = Self::eqexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("neq".into())),
                Box::new(Self::Tuple(vec![rel, end])),
            ))
        } else if let Some(()) = t.consume(Token::Equal) {
            let end = Self::eqexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("eq".into())),
                Box::new(Self::Tuple(vec![rel, end])),
            ))
        } else {
            Ok(rel)
        }
    }

    fn relexpr(t: &mut TokenStream) -> Result<Self, String> {
        let conc = Self::addexpr(t)?;

        if let Some(()) = t.consume(Token::LArrow) {
            let end = Self::relexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("lt".into())),
                Box::new(Self::Tuple(vec![conc, end])),
            ))
        } else if let Some(()) = t.consume(Token::RArrow) {
            let end = Self::relexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("gt".into())),
                Box::new(Self::Tuple(vec![conc, end])),
            ))
        } else if let Some(()) = t.consume(Token::LTE) {
            let end = Self::relexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("leq".into())),
                Box::new(Self::Tuple(vec![conc, end])),
            ))
        } else if let Some(()) = t.consume(Token::GTE) {
            let end = Self::relexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("geq".into())),
                Box::new(Self::Tuple(vec![conc, end])),
            ))
        } else {
            Ok(conc)
        }
    }

    fn addexpr(t: &mut TokenStream) -> Result<Self, String> {
        let mul = Self::mulexpr(t)?;

        if let Some(()) = t.consume(Token::Plus) {
            let end = Self::addexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("add".into())),
                Box::new(Self::Tuple(vec![mul, end])),
            ))
        } else if let Some(()) = t.consume(Token::Sub) {
            let end = Self::addexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("sub".into())),
                Box::new(Self::Tuple(vec![mul, end])),
            ))
        } else {
            Ok(mul)
        }
    }

    fn mulexpr(t: &mut TokenStream) -> Result<Self, String> {
        let pow = Self::powexpr(t)?;

        if let Some(()) = t.consume(Token::Mul) {
            let end = Self::mulexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("mul".into())),
                Box::new(Self::Tuple(vec![pow, end])),
            ))
        } else if let Some(()) = t.consume(Token::Div) {
            let end = Self::mulexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("div".into())),
                Box::new(Self::Tuple(vec![pow, end])),
            ))
        } else if let Some(()) = t.consume(Token::Mod) {
            let end = Self::mulexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("mod".into())),
                Box::new(Self::Tuple(vec![pow, end])),
            ))
        } else {
            Ok(pow)
        }
    }

    fn powexpr(t: &mut TokenStream) -> Result<Self, String> {
        let unary = Self::unary(t)?;

        if let Some(()) = t.consume(Token::Pow) {
            let end = Self::powexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("pow".into())),
                Box::new(Self::Tuple(vec![unary, end])),
            ))
        } else {
            Ok(unary)
        }
    }

    fn unary(t: &mut TokenStream) -> Result<Self, String> {
        if let Some(()) = t.consume(Token::Not) {
            let un = Self::unary(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("not".into())),
                Box::new(un),
            ))
        } else if let Some(()) = t.consume(Token::BitNot) {
            let un = Self::unary(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("bitnot".into())),
                Box::new(un),
            ))
        } else if let Some(()) = t.consume(Token::Sub) {
            let un = Self::unary(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("neg".into())),
                Box::new(un),
            ))
        } else {
            Ok(Self::postfix(t)?)
        }
    }

    fn postfix(t: &mut TokenStream) -> Result<Self, String> {
        let primary = Self::primary(t)?;
        Self::postfix_post(t, primary)
    }

    fn postfix_post(t: &mut TokenStream, primary: Expression) -> Result<Self, String> {
        let pfix = if t.consume(Token::LParen).is_some() {
            // parse a call with a tuple
            let tup = if let Some(()) = t.consume(Token::RParen) {
                Self::Unit
            } else {
                let mut es = Vec::new();
                let e = Self::parse(t)?;
                es.push(e);

                while t.consume(Token::Comma).is_some() {
                    es.push(Self::parse(t)?);
                }

                t.assert(Token::RParen)?;

                if es.len() == 1 {
                    es.into_iter().next().unwrap()
                } else {
                    Self::Tuple(es)
                }
            };

            Self::Call(Box::new(primary), Box::new(tup))
        } else if t.consume(Token::Concat).is_some() {
            // parse a concat expression
            let end = Self::parse(t)?;
            Self::Call(
                Box::new(Self::Identifier("Cons".into())),
                Box::new(Self::Tuple(vec![primary, end])),
            )
        } else if t.consume(Token::Dot).is_some() {
            let func = Expression::Identifier(t.ident()?);

            let mut es = vec![];
            t.assert(Token::LParen)?;

            while !t.test(Token::RParen) {
                es.push(Expression::parse(t)?);
                if t.consume(Token::Comma).is_none() {
                    break;
                }
            }
            t.assert(Token::RParen)?;

            let args = match es.len() {
                0 => primary,
                _ => {
                    es.insert(0, primary);
                    Expression::Tuple(es)
                }
            };

            Expression::Call(Box::new(func), Box::new(args))
        } else if t.consume(Token::Question).is_some() {
            let then = Expression::parse(t)?;

            t.assert(Token::Colon)?;

            let else_ = Expression::parse(t)?;

            Self::If(Box::new(primary), Box::new(then), Box::new(else_))
        } else if t.consume(Token::FatArrow).is_some() {
            // Fancy call with primary as first arg.

            // must be followed by an identifer and then some args
            let f = t.ident()?;

            // Get args in tuple
            let mut args = vec![primary];

            t.assert(Token::LParen)?;
            if let Some(()) = t.consume(Token::RParen) {
            } else {
                args.push(Self::parse(t)?);
                while t.consume(Token::Comma).is_some() {
                    args.push(Self::parse(t)?);
                }
                t.assert(Token::RParen)?;
            }

            let args = Self::Tuple(args);

            Self::Call(Box::new(Self::Identifier(f)), Box::new(args))
        } else if t.consume(Token::Arrow).is_some() {
            // parse lambda expression
            let pat = primary.to_lambda_pattern();
            let end = Self::parse(t)?;

            Self::Lambda(pat, Box::new(end))
        } else {
            return Ok(primary);
        };

        Self::postfix_post(t, pfix)
    }

    fn primary(t: &mut TokenStream) -> Result<Self, String> {
        let next = match t.next() {
            Some(t) => t,
            None => return Err("".to_string()),
        };

        match next {
            // Let statement
            Lexeme { token: Token::Let } => {
                let pat = Pattern::parse(t)?;

                t.assert(Token::Assign)?;

                let e = Self::parse(t)?;

                t.assert(Token::In)?;

                let body = Self::parse(t)?;

                Ok(Self::Let(pat, Box::new(e), Box::new(body)))
            }
            // If statement
            Lexeme { token: Token::If } => {
                let cond = Self::parse(t)?;

                t.assert(Token::Then)?;

                let then = Self::parse(t)?;

                t.assert(Token::Else)?;

                let else_ = Self::parse(t)?;

                Ok(Self::If(Box::new(cond), Box::new(then), Box::new(else_)))
            }
            // Match statement
            Lexeme {
                token: Token::Match,
            } => {
                let match_ = Self::parse(t)?;

                t.assert(Token::With)?;

                let pat = Pattern::parse(t)?;
                t.assert(Token::Colon)?;
                let e = Self::parse(t)?;

                let mut cases = vec![(pat, e)];

                while t.consume(Token::Comma).is_some() {
                    let pat = Pattern::parse(t)?;
                    t.assert(Token::Colon)?;
                    let e = Self::parse(t)?;
                    cases.push((pat, e));
                }

                Ok(Self::Match(Box::new(match_), cases))
            }
            // String literal
            Lexeme {
                token: Token::String(s),
                ..
            } => Ok(Self::cons_from_str(&s)),
            // Number literal
            Lexeme {
                token: Token::Num(n),
                ..
            } => Ok(Self::Num(n)),
            // Identifier
            Lexeme {
                token: Token::Ident(i),
                ..
            } => {
                if i.chars().next().unwrap().is_uppercase() && !t.test(Token::LParen) {
                    Ok(Self::Call(
                        Box::new(Self::Identifier(i)),
                        Box::new(Self::Unit),
                    ))
                } else {
                    Ok(Self::Identifier(i))
                }
            }
            // Tuple
            Lexeme {
                token: Token::LParen,
                ..
            } => {
                if let Some(()) = t.consume(Token::RParen) {
                    Ok(Self::Unit)
                } else {
                    let mut es = Vec::new();
                    let e = Self::parse(t)?;
                    es.push(e);

                    while t.consume(Token::Comma).is_some() {
                        es.push(Self::parse(t)?);
                    }

                    t.assert(Token::RParen)?;

                    if es.len() == 1 {
                        Ok(es.into_iter().next().unwrap())
                    } else {
                        Ok(Self::Tuple(es))
                    }
                }
            }
            // List
            Lexeme {
                token: Token::LBrace,
            } => {
                let mut es = Vec::new();

                while !t.test(Token::RBrace) {
                    es.push(Self::parse(t)?);
                    if t.consume(Token::Comma).is_none() {
                        break;
                    }
                }
                t.assert(Token::RBrace)?;

                Ok(Self::cons_from_es(&es))
            }
            // otherwise error
            a => {
                //panic!("PrimaryExpr: Expected identifier, constant, or expression, found: {:?}", a);
                Err(format!("Expected expression, found '{}'", a.token.name()))
            }
        }
    }

    pub fn cons_from_str(s: &str) -> Self {
        let nums = s
            .chars()
            .map(|c| c as u64)
            .map(|i| Self::Num(i))
            .map(|i| Self::Call(Box::new(Self::Identifier("Char".to_string())), Box::new(i)))
            .collect::<Vec<_>>();

        Self::cons_from_es(&nums)
    }

    pub fn cons_from_es(es: &[Self]) -> Self {
        if es.is_empty() {
            return Self::Call(
                Box::new(Self::Identifier("Nil".to_string())),
                Box::new(Self::Unit),
            );
        }

        Self::Call(
            Box::new(Self::Identifier("Cons".to_string())),
            Box::new(Self::Tuple(vec![
                es[0].clone(),
                Self::cons_from_es(&es[1..]),
            ])),
        )
    }

    fn to_lambda_pattern(&self) -> Pattern {
        match self {
            Self::Identifier(s) => Pattern::Var(s.clone(), None),
            Self::Tuple(es) => {
                Pattern::Tuple(es.iter().map(|e| e.to_lambda_pattern()).collect(), None)
            }
            Self::Unit => Pattern::Unit(Some(Type::Unit)),
            Self::Call(f, args) => {
                if let Expression::Identifier(s) = &**f {
                    Pattern::Cons(s.clone(), Box::new(args.to_lambda_pattern()), None)
                } else {
                    panic!("lambda what?")
                }
            }
            _ => panic!("ahh"),
        }
    }
}

impl Pattern {
    pub fn cons_from_str(s: &str) -> Self {
        let nums = s
            .chars()
            .map(|c| c as u64)
            .map(|i| Self::Num(i, None))
            .collect::<Vec<_>>();

        Self::cons_from_es(&nums)
    }

    pub fn cons_from_es(es: &[Self]) -> Self {
        if es.is_empty() {
            return Self::Cons("Nil".to_string(), Box::new(Self::Unit(None)), None);
        }

        Self::Cons(
            "Cons".to_string(),
            Box::new(Self::Tuple(
                vec![es[0].clone(), Self::cons_from_es(&es[1..])],
                None,
            )),
            None,
        )
    }

    fn qualify(self, prefix: &str, me: &ParseTree) -> Self {
        match self {
            Pattern::Tuple(ps, t) => {
                Pattern::Tuple(ps.into_iter().map(|p| p.qualify(prefix, me)).collect(), t)
            }
            Pattern::Cons(name, args, t) => {
                let name = if me
                    .types
                    .iter()
                    .map(|(_, a)| a)
                    .any(|data| data.has_cons(&name))
                {
                    prefixed(prefix, &name)
                } else {
                    name
                };

                Pattern::Cons(name, Box::new(args.qualify(prefix, me)), t)
            }
            a => a,
        }
    }

    fn resolve(
        self,
        rt: &mut HashMap<String, DataDecl>,
        mods: &HashMap<String, ParseTree>,
    ) -> Self {
        match self {
            Pattern::Namespace(ns, p, _) => {
                if let Pattern::Cons(n, args, t) = *p {
                    let newt = mods[&ns]
                        .types
                        .iter()
                        .find(|(n2, _)| *n2 == n)
                        .map(|(_, t)| t.clone())
                        .unwrap()
                        .resolve(rt, mods)
                        .qualify(&ns, &mods[&ns]);
                    rt.insert(format!("{ns}.{n}"), newt);
                    Pattern::Cons(format!("{ns}.{n}"), args, t)
                } else {
                    panic!()
                }
            }
            Pattern::Tuple(ps, t) => {
                Pattern::Tuple(ps.into_iter().map(|p| p.resolve(rt, mods)).collect(), t)
            }
            Pattern::Cons(n, args, t) => Pattern::Cons(n, Box::new(args.resolve(rt, mods)), t),
            a => a,
        }
    }

    fn parse(t: &mut TokenStream) -> Result<Pattern, String> {
        let x = Self::parse_base(t)?;

        if t.consume(Token::Concat).is_some() {
            let xs = Self::parse(t)?;
            return Ok(Self::Cons(
                "Cons".into(),
                Box::new(Pattern::Tuple(vec![x, xs], None)),
                None,
            ));
        }

        Ok(x)
    }

    fn parse_tuple(t: &mut TokenStream) -> Result<Pattern, String> {
        t.assert(Token::LParen)?;
        // We are either the unit type or the tuple type

        if let Some(()) = t.consume(Token::RParen) {
            return Ok(Pattern::Unit(Some(Type::Unit)));
        }

        let mut pats = Vec::new();
        let pat = Pattern::parse(t)?;
        pats.push(pat);

        while let Some(()) = t.consume(Token::Comma) {
            let pat = Pattern::parse(t)?;
            pats.push(pat);
        }

        t.assert(Token::RParen)?;

        if pats.len() == 1 {
            Ok(pats.into_iter().next().unwrap())
        } else {
            Ok(Pattern::Tuple(pats, None))
        }
    }

    fn parse_base(t: &mut TokenStream) -> Result<Pattern, String> {
        if t.test(Token::LParen) {
            return Self::parse_tuple(t);
        }

        match t.next() {
            Some(Lexeme {
                token: Token::LBrace,
                ..
            }) => {
                t.assert(Token::RBrace)?;
                Ok(Pattern::Cons(
                    "Nil".to_string(),
                    Box::new(Self::Unit(Some(Type::Unit))),
                    None,
                ))
            }
            Some(Lexeme {
                token: Token::Underscore,
            }) => Ok(Pattern::Any(None)),
            Some(Lexeme {
                token: Token::Num(n),
                ..
            }) => Ok(Pattern::Num(n, Some(Type::I32))),
            Some(Lexeme {
                token: Token::String(s),
                ..
            }) => Ok(Pattern::cons_from_str(&s)),
            Some(Lexeme {
                token: Token::Ident(mut i),
                ..
            }) => {
                while t.consume(Token::Dot).is_some() {
                    i.push_str(".");
                    i.push_str(&t.ident()?);
                }

                if let Some((ns, f)) = i.rsplit_once(".") {
                    // This is a namespaced constructor
                    let args = if t.test(Token::LParen) {
                        Pattern::parse_tuple(t)?
                    } else {
                        Pattern::Unit(Some(Type::Unit))
                    };

                    Ok(Pattern::Namespace(
                        ns.to_string(),
                        Box::new(Pattern::Cons(f.to_string(), Box::new(args), None)),
                        None,
                    ))
                } else {
                    // either a variable or a constructor
                    // lets enforce that constructors *must* start with a capital
                    // and that variables have to start with lowercase
                    if i.chars().next().unwrap().is_uppercase() {
                        // This is a namespaced constructor
                        let args = if t.test(Token::LParen) {
                            Pattern::parse_tuple(t)?
                        } else {
                            Pattern::Unit(Some(Type::Unit))
                        };
                        Ok(Pattern::Cons(i, Box::new(args), None))
                    } else {
                        Ok(Pattern::Var(i, None))
                    }
                }
            }
            a => panic!("unexpected token: {a:?} {:?} {:?}", t.next(), t.next()),
        }
    }
}
