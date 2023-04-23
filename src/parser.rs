use std::collections::HashMap;

use crate::Token;
use crate::lexer::TokenStream;

use crate::ast::{
    ProgramTree,
    Trait,
    DataDecl,
    TypeCons,
    Type,
    FunctionDef,
    Expression,
    Pattern,
};

use rand::{distributions::Alphanumeric, Rng};

impl ProgramTree {
    pub fn parse(t: &mut TokenStream) -> Self {
        let mut me = Self {
            traits: HashMap::new(),
            impls: HashMap::new(),
            types: HashMap::new(),
            typedefs: HashMap::new(),
            funcs: HashMap::new(),
            defs: HashMap::new(),
        };

        while *t.peek() != Token::EOF {
            match t.peek().clone() {
                Token::Trait => {
                    let t = Trait::parse(t);
                    me.traits.insert(t.name.clone(), t);
                }
                Token::Impl => {
                    t.adv();

                    let trait_name = t.peek().ident().clone();
                    t.adv();

                    assert_eq!(*t.peek(), Token::For);
                    t.adv();

                    let var = Type::parse(t);

                    // create random suffx
                    let suffix = rand::thread_rng()
                        .sample_iter(&Alphanumeric)
                        .take(8)
                        .map(char::from)
                        .collect::<String>();

                    let mut subs = Vec::new();

                    // Emit new type
                    let reftrait = me.traits.get(&trait_name).unwrap();
                    let from = &reftrait.var;
                    for (name, t) in reftrait.types.iter() {
                        let newt = t.substitute(from, &var);
                        let mut newname = name.clone();
                        newname.push('_');
                        newname.push_str(&suffix);
                        subs.push((name, newname.clone()));
                        me.typedefs.insert(newname, newt);
                    }

                    // Emit trait functions
                    for (name, f) in reftrait.funcs.iter() {
                        let mut newname = name.clone();
                        newname.push('_');
                        newname.push_str(&suffix);

                        let funs = f.iter().map(|fun| {
                            let mut fun = fun.clone();
                            for (from, to) in subs.iter() {
                                fun = fun.substitute(from, to);
                            }

                            fun
                        }).collect();

                        me.funcs.insert(newname, funs);
                    }

                    assert_eq!(*t.peek(), Token::LCurly);
                    t.adv();

                    // Emit impl functions
                    while *t.peek() != Token::RCurly {
                        let mut func = FunctionDef::parse(t);
                        for (from, to) in subs.iter() {
                            func = func.substitute(from, to);
                        }
                        
                        if let Some(f) = me.funcs.get_mut(&func.name) {
                            f.push(func);
                        } else {
                            me.funcs.insert(func.name.clone(), vec![func]);
                        }
                    }
                    t.adv();

                    // Add to list of implementations
                    if let Some(i) = me.impls.get_mut(&trait_name) {
                        i.push((suffix, var));
                    } else {
                        me.impls.insert(trait_name, vec![(suffix, var)]);
                    }
                }
                Token::Type => {
                    // Either a typedecl or datadecl
                    t.adv();

                    let name = t.peek().ident().clone();
                    t.adv();

                    // generic args for forall type
                    let mut args = Vec::new();
                    if *t.peek() == Token::LArrow {
                        t.adv();

                        let arg = t.peek().ident().clone();
                        t.adv();
                        args.push(arg);

                        while *t.peek() == Token::Comma {
                            t.adv();

                            let arg = t.peek().ident().clone();
                            t.adv();
                            args.push(arg);
                        }

                        assert_eq!(*t.peek(), Token::RArrow);
                        t.adv();
                    }

                    match t.peek().clone() {
                        Token::Assign => {
                            t.adv();
                            let ty = DataDecl::parse(t, args);
                            me.types.insert(name, ty);
                        }
                        Token::Colon => {
                            t.adv();
                            let ty = Type::parse(t);
                            me.typedefs.insert(name, Type::ForAll(args, Box::new(ty)));
                        }
                        a => panic!("expected colon or equals, found {a:?}")
                    }
                }
                Token::Def => {
                    t.adv();

                    let name = t.peek().ident().clone();
                    t.adv();

                    let expr = Expression::parse(t);
                    me.defs.insert(name, expr);
                }
                Token::Ident(_) => {
                    let func = FunctionDef::parse(t);
                    if let Some(f) = me.funcs.get_mut(&func.name) {
                        f.push(func);
                    } else {
                        me.funcs.insert(func.name.clone(), vec![func]);
                    }
                }
                a => {
                    println!("{a:?}");
                    panic!("Ahhh")
                }
            }
        }

        me
    }
}

impl Trait {
    fn parse(t: &mut TokenStream) -> Self {
        assert_eq!(*t.peek(), Token::Trait);
        t.adv();

        let name = t.peek().ident().clone();
        t.adv();

        assert_eq!(*t.peek(), Token::LArrow);
        t.adv();

        let var = t.peek().ident().clone();
        t.adv();

        assert_eq!(*t.peek(), Token::RArrow);
        t.adv();

        assert_eq!(*t.peek(), Token::LCurly);
        t.adv();

        let mut types = HashMap::new();
        let mut funcs = HashMap::<String, Vec<FunctionDef>>::new();

        loop {
            match *t.peek() {
                Token::RCurly => {
                    t.adv();
                    break;
                },
                Token::Type => {
                    // typedecls
                    t.adv();

                    let name = t.peek().ident().clone();
                    t.adv();

                    assert_eq!(*t.peek(), Token::Colon);
                    t.adv();

                    let ty = Type::parse(t);
                    types.insert(name, ty);
                }
                Token::Ident(_) => {
                    let func = FunctionDef::parse(t);
                    if let Some(f) = funcs.get_mut(&func.name) {
                        f.push(func);
                    } else {
                        funcs.insert(func.name.clone(), vec![func]);
                    }
                }
                _ => {panic!("Unexpected token")}
            }
        }

        Trait {
            name,
            var,
            types,
            funcs,
        }
    }
}

impl DataDecl {
    fn parse(t: &mut TokenStream, args: Vec<String>) -> Self {
        let mut cons = Vec::new();
        cons.push(TypeCons::parse(t));

        while *t.peek() == Token::Bar {
            t.adv();
            cons.push(TypeCons::parse(t));
        }

        Self { cons, args }
    }
}

impl TypeCons {
    fn parse(t: &mut TokenStream) -> Self {
        let name = t.peek().ident().clone();
        t.adv();

        let mut args = Vec::new();
        if *t.peek() == Token::LParen {
            t.adv();

            args.push(Type::parse(t));

            while *t.peek() == Token::Comma {
                t.adv();
                args.push(Type::parse(t));
            }

            assert_eq!(*t.peek(), Token::RParen);
            t.adv();
        }

        Self { name, args }
    }
}

impl FunctionDef {
    fn parse(t: &mut TokenStream) -> Self {
        if let Token::Ident(name) = t.peek().clone() {
            t.adv();

            assert_eq!(*t.peek(), Token::LParen);
            let args = Pattern::parse(t);

            assert_eq!(*t.peek(), Token::Assign);
            t.adv();
            
            let mut body = Vec::new();
            if *t.peek() == Token::LCurly {
                t.adv();

                while *t.peek() != Token::RCurly {
                    body.push(Expression::parse(t));
                }

                assert_eq!(*t.peek(), Token::RCurly);
                t.adv();
            } else {
                body.push(Expression::parse(t));
            }

            return FunctionDef {name, args, body}
        }

        panic!("Failed to parse func declaration");
    }

    fn substitute(&self, from: &str, to: &str) -> Self {
        let name = if self.name == from { to.to_string() } else {self.name.clone()};

        FunctionDef {
            name,
            body: self.body.clone(),
            args: self.args.clone(),
        }
    }
}

impl Type {
    fn parse(t: &mut TokenStream) -> Self {
        let cont = Self::parse_tuple(t);

        if *t.peek() == Token::Arrow {
            t.adv();
            let end = Self::parse_tuple(t);

            Self::Arrow(Box::new(cont), Box::new(end))
        } else {
            cont
        }
    }

    fn parse_tuple(t: &mut TokenStream) -> Self {
        if *t.peek() == Token::LParen {
            t.adv();

            if *t.peek() == Token::RParen {
                // Not a tuple, en empty type
                t.adv();
                return Self::Unit;
            }

            let mut inner = vec![Self::parse(t)];

            // Parse comma separated fields
            while *t.peek() == Token::Comma {
                t.adv();
                inner.push(Self::parse(t));
            }

            assert_eq!(*t.peek(), Token::RParen);
            t.adv();
            
            Self::Tuple(inner)
        } else {
            Self::parse_list(t)
        }
    }

    fn parse_list(t: &mut TokenStream) -> Self {
        if *t.peek() == Token::LBrace {
            t.adv();

            let inner = Self::parse(t);

            assert_eq!(*t.peek(), Token::RBrace);
            t.adv();

            Self::List(Box::new(inner))
        } else {
            Self::parse_generic(t)
        }
    }

    fn parse_generic(t: &mut TokenStream) -> Self {
        let base = Self::parse_base(t);

        if *t.peek() == Token::LArrow {
            t.adv();
            let mut vars = Vec::new();
            vars.push(Self::parse(t));

            while *t.peek() == Token::Comma {
                t.adv();
                vars.push(Self::parse(t));
            }

            assert_eq!(*t.peek(), Token::RArrow);
            t.adv();
            
            Self::Generic(vars, Box::new(base))
        } else {
            base
        }
    }

    fn parse_base(t: &mut TokenStream) -> Self {
        let out = match t.peek().clone() {
            Token::Ident(i) => Self::Ident(i),
            Token::U8 => Self::U8,
            Token::U16 => Self::U16,
            Token::U32 => Self::U32,
            Token::U64 => Self::U64,
            Token::I8 => Self::I8,
            Token::I16 => Self::I16,
            Token::I32 => Self::I32,
            Token::I64 => Self::I64,
            Token::Str => Self::Str,
            _ => { panic!("parse_base: Unexpected token") }
        };

        t.adv();
        out
    }

    fn substitute(&self, from: &str, to: &Type) -> Self {
        match self {
            Self::Arrow(l, r) => {
                Self::Arrow(
                    Box::new(l.substitute(from, to)),
                    Box::new(r.substitute(from, to))
                )
            }
            Self::Ident(x) if x==from => {
                to.clone()
            }
            Self::List(t) => {
                Self::List(Box::new(t.substitute(from, to)))
            }
            Self::Tuple(t) => {
                Self::Tuple(
                    t.iter().map(|ty| ty.substitute(from, to)).collect()
                )
            }
            Self::ForAll(vars, t) => {
                let v: Vec<_> = vars.iter()
                    .filter(|s| *s!=from)
                    .map(|s| s.clone())
                    .collect();

                if v.len() == 0 {
                    t.substitute(from, to)
                } else {
                    Self::ForAll(v, Box::new(t.substitute(from, to)))
                }
            }
            _ => {self.clone()}
        }
    }
}


impl Expression {
    pub fn parse(t: &mut TokenStream) -> Self {
        // Start with let expression
        if *t.peek() == Token::Let {
            t.adv();

            let pat = Pattern::parse(t);

            assert_eq!(*t.peek(), Token::Assign);
            t.adv();

            Self::Let(pat, Box::new(Self::orexpr(t)))
        } else {
            Self::tuple(t)
        }
    }

    pub fn tuple(t: &mut TokenStream) -> Self {
        if *t.peek() == Token::LParen {
            t.adv();

            let mut es = Vec::new();
            es.push(Self::parse(t));

            while *t.peek() == Token::Comma {
                t.adv();
                es.push(Self::parse(t));
            }

            assert_eq!(*t.peek(), Token::RParen);
            t.adv();

            if es.len() == 1 {
                es[0].clone()
            } else {
                Self::Tuple(es)
            }
        } else {
            Self::orexpr(t)
        }
    }

    pub fn orexpr(t: &mut TokenStream) -> Self {
        let and = Self::andexpr(t);

        if *t.peek() == Token::Or {
            t.adv();
            let end = Self::parse(t);
            Self::Call(
                Box::new(Self::Identifier("or".into())),
                vec![and, end]
            )
        } else {
            and
        }
    }

    fn andexpr(t: &mut TokenStream) -> Self {
        let bitor = Self::bitorexpr(t);

        if *t.peek() == Token::And {
            t.adv();
            let end = Self::andexpr(t);
            Self::Call(
                Box::new(Self::Identifier("and".into())),
                vec![bitor, end]
            )
        } else {
            bitor
        }
    }

    fn bitorexpr(t: &mut TokenStream) -> Self {
        let xor = Self::bitxorexpr(t);

        if *t.peek() == Token::Bar {
            t.adv();
            let end = Self::bitorexpr(t);
            Self::Call(
                Box::new(Self::Identifier("bitor".into())),
                vec![xor, end]
            )
        } else {
            xor
        }
    }

    fn bitxorexpr(t: &mut TokenStream) -> Self {
        let and = Self::bitandexpr(t);

        if *t.peek() == Token::BitXor {
            t.adv();
            let end = Self::bitxorexpr(t);
            Self::Call(
                Box::new(Self::Identifier("bitxor".into())),
                vec![and, end]
            )
        } else {
            and
        }
    }

    fn bitandexpr(t: &mut TokenStream) -> Self {
        let eq = Self::eqexpr(t);

        if *t.peek() == Token::BitAnd {
            t.adv();
            let end = Self::bitandexpr(t);
            Self::Call(
                Box::new(Self::Identifier("bitand".into())),
                vec![eq, end]
            )
        } else {
            eq
        }
    }

    fn eqexpr(t: &mut TokenStream) -> Self {
        let rel = Self::relexpr(t);

        match *t.peek() {
            Token::NotEqual => {
                t.adv();
                let end = Self::eqexpr(t);
                Self::Call(
                    Box::new(Self::Identifier("neq".into())),
                    vec![rel, end]
                )
            }
            Token::Equal => {
                t.adv();
                let end = Self::eqexpr(t);
                Self::Call(
                    Box::new(Self::Identifier("eq".into())),
                    vec![rel, end]
                )
            }
            _ => {
                rel
            }
        }
    }

    fn relexpr(t: &mut TokenStream) -> Self {
        let conc = Self::concexpr(t);
        
        match *t.peek() {
            Token::LArrow => {
                t.adv();
                let end = Self::relexpr(t);
                Self::Call(
                    Box::new(Self::Identifier("lt".into())),
                    vec![conc, end]
                )
            }
            Token::RArrow => {
                t.adv();
                let end = Self::relexpr(t);
                Self::Call(
                    Box::new(Self::Identifier("gt".into())),
                    vec![conc, end]
                )
            }
            Token::LTE => {
                t.adv();
                let end = Self::relexpr(t);
                Self::Call(
                    Box::new(Self::Identifier("leq".into())),
                    vec![conc, end]
                )
            }
            Token::GTE => {
                t.adv();
                let end = Self::relexpr(t);
                Self::Call(
                    Box::new(Self::Identifier("geq".into())),
                    vec![conc, end]
                )
            }
            _ => {
                conc 
            }
        }
    }

    fn concexpr(t: &mut TokenStream) -> Self {
        let add = Self::addexpr(t);

        if *t.peek() == Token::Concat {
            t.adv();
            let end = Self::concexpr(t);
            Self::Call(
                Box::new(Self::Identifier("Cons".into())),
                vec![add, end]
            )
        } else {
            add
        }
    }

    fn addexpr(t: &mut TokenStream) -> Self {
        let mul = Self::mulexpr(t);

        match *t.peek() {
            Token::Plus => {
                t.adv();
                let end = Self::addexpr(t);
                Self::Call(
                    Box::new(Self::Identifier("add".into())),
                    vec![mul, end]
                )
            }
            Token::Sub => {
                t.adv();
                let end = Self::addexpr(t);
                Self::Call(
                    Box::new(Self::Identifier("sub".into())),
                    vec![mul, end]
                )
            }
            _ => {
                mul
            }
        }
    }

    fn mulexpr(t: &mut TokenStream) -> Self {
        let pow = Self::powexpr(t);

        match *t.peek() {
            Token::Mul => {
                t.adv();
                let end = Self::mulexpr(t);
                Self::Call(
                    Box::new(Self::Identifier("mul".into())),
                    vec![pow, end]
                )
            }
            Token::Div => {
                t.adv();
                let end = Self::mulexpr(t);
                Self::Call(
                    Box::new(Self::Identifier("div".into())),
                    vec![pow, end]
                )
            }
            Token::Mod => {
                t.adv();
                let end = Self::mulexpr(t);
                Self::Call(
                    Box::new(Self::Identifier("mod".into())),
                    vec![pow, end]
                )
            }
            _ => { pow }
        }
    }

    fn powexpr(t: &mut TokenStream) -> Self {
        let unary = Self::unary(t);

        if *t.peek() == Token::Pow {
            t.adv();
            let end = Self::powexpr(t);
            Self::Call(
                Box::new(Self::Identifier("pow".into())),
                vec![unary, end]
            )
        } else {
            unary
        }
    }

    fn unary(t: &mut TokenStream) -> Self {
        match *t.peek() {
            Token::Not => {
                t.adv();
                let un = Self::unary(t);
                Self::Call(
                    Box::new(Self::Identifier("not".into())),
                    vec![un]
                )
            }
            Token::BitNot => {
                t.adv();
                let un = Self::unary(t);
                Self::Call(
                    Box::new(Self::Identifier("bitnot".into())),
                    vec![un]
                )
            }
            Token::Sub => {
                t.adv();
                let un = Self::unary(t);
                Self::Call(
                    Box::new(Self::Identifier("neg".into())),
                    vec![un]
                )
            }
            _ => { Self::postfix(t) }
        }
    }

    fn postfix(t: &mut TokenStream) -> Self {
        let primary = Self::primary(t);

        match t.peek() {
            Token::LParen => {
                t.adv();

                let al = if *t.peek() == Token::RParen {
                    vec![]
                } else {
                    ArgList::parse(t)
                };

                assert_eq!(*t.peek(), Token::RParen);
                t.adv();

                Self::Call(Box::new(primary), al)
            }
            Token::Dot => {
                t.adv();

                let call = Self::postfix(t);
                match call {
                    Self::Call(f, mut args) => {
                        args.insert(0, primary);
                        Self::Call(f, args)
                    }
                    _ => {panic!("expected call")}
                }
            }
            _ => primary
        }
    }

    fn primary(t: &mut TokenStream) -> Self {
        match t.peek().clone() {
            Token::String(s) => {
                t.adv();
                Self::Str(s.clone())
            }
            Token::Num(n) => {
                t.adv();
                Self::Num(n)
            }
            Token::Ident(i) => {
                t.adv();
                Self::Identifier(i.clone())
            }
            Token::LParen => {
                t.adv();
                let e = Expression::parse(t);
                assert_eq!(*t.peek(), Token::RParen);
                t.adv();
                e
            }
            Token::LBrace => {
                t.adv();
                assert_eq!(*t.peek(), Token::RBrace);
                t.adv();
                Self::EmptyList
            }
            _ => {
                panic!("PrimaryExpr: Expected identifier, constant, or expression")
            }
        }
    }

    fn substitute(&self, from: &str, to: &str) -> Self {
        match self {
            Self::Identifier(i) => {
                if i == from {
                    Self::Identifier(to.to_string())
                } else {
                    Self::Identifier(i.clone())
                }
            }
            Self::Tuple(es) => {
                Self::Tuple(
                    es.iter().map(|e| e.substitute(from, to)).collect()
                )
            }
            Self::List(es) => {
                Self::List(
                    es.iter().map(|e| e.substitute(from, to)).collect()
                )
            }
            Self::Let(p, e) => {
                Self::Let(p.clone(), Box::new(e.substitute(from, to)))
            }
            Self::Match(e, cases) => {
                Self::Match(
                    Box::new(e.substitute(from, to)),
                    cases.iter().map(|(pat, exp)| (pat.clone(), exp.substitute(from, to))).collect()
                )
            }
            Self::Call(e, args) => {
                Self::Call(
                    Box::new(e.substitute(from, to)),
                    args.iter().map(|e| e.substitute(from, to)).collect()
                )
            }
            Self::Lambda(pats, exp) => {
                Self::Lambda(pats.clone(), Box::new(exp.substitute(from, to)))
            }
            _ => self.clone()
        }
    }
}


impl Pattern {
    fn parse(t: &mut TokenStream) -> Pattern {
        if *t.peek() == Token::LParen {
            t.adv();
            // We are either the unit type or the tuple type

            if *t.peek() == Token::RParen {
                t.adv();
                return Pattern::Unit;
            }

            let mut pats = Vec::new();
            pats.push(Pattern::parse_conc(t));

            while *t.peek() == Token::Comma {
                t.adv();
                pats.push(Pattern::parse_conc(t));
            }

            assert_eq!(*t.peek(), Token::RParen);
            t.adv();

            if pats.len() == 1 {
                pats[0].clone()
            } else {
                Pattern::Tuple(pats)
            }
        } else {
            Pattern::parse_conc(t)
        }
    }

    fn parse_conc(t: &mut TokenStream) -> Pattern {
        let a = Self::parse_base(t);

        if *t.peek() == Token::Concat {
            t.adv();
            let b = Self::parse_base(t);

            Self::Cons(
                "Cons".into(),
                Box::new(Pattern::Tuple(vec![a, b]))
            )
        } else {
            a
        }
    }

    fn parse_base(t: &mut TokenStream) -> Pattern {
        match t.peek().clone() {
            Token::LBrace => {
                t.adv();
                assert_eq!(*t.peek(), Token::RBrace);
                t.adv();
                Pattern::EmptyList
            }
            Token::Num(n) => {
                t.adv();
                Pattern::Num(n)
            }
            Token::String(s) => {
                t.adv();
                Pattern::Str(s)
            }
            Token::Ident(i) => {
                t.adv();
                // either variable or constructor...
                if *t.peek() == Token::LParen {
                    let pat = Pattern::parse(t);
                    Pattern::Cons(i, Box::new(pat))
                } else {
                    Pattern::Var(i)
                }
            }
            _ => panic!("unexpected token")
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct ArgList;
impl ArgList {
    fn parse(t: &mut TokenStream) -> Vec<Expression> {
        let mut exprs = Vec::new();
        exprs.push(Expression::parse(t));

        while *t.peek() == Token::Comma {
            t.adv();
            exprs.push(Expression::parse(t));
        }

        exprs
    }
}

// Tests
#[allow(dead_code)]
fn s_to_stream(s: &str) -> TokenStream {
    use crate::Lexer;
    let mut l = Lexer::default();
    l.lex(s)
}

#[test]
fn test_parse_type() {
    eprintln!("Test parsing builtin type");
    assert_eq!(
        Type::parse(&mut s_to_stream("u8")),
        Type::U8
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("u16")),
        Type::U16
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("u32")),
        Type::U32
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("u64")),
        Type::U64
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("i8")),
        Type::I8
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("i16")),
        Type::I16
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("i32")),
        Type::I32
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("i64")),
        Type::I64
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("()")),
        Type::Unit
    );

    eprintln!("Test parsing list type");
    assert_eq!(
        Type::parse(&mut s_to_stream("[i64]")),
        Type::List(Box::new(Type::I64))
    );

    eprintln!("Test parsing identifier type");
    assert_eq!(
        Type::parse(&mut s_to_stream("x")),
        Type::Ident("x".to_string())
    );

    eprintln!("Test parsing tuple type");
    assert_eq!(
        Type::parse(&mut s_to_stream("(x, y)")),
        Type::Tuple(vec![
            Type::Ident("x".into()),
            Type::Ident("y".into())
        ])
    );

    assert_eq!(
        Type::parse(&mut s_to_stream("(i32, [i32])")),
        Type::Tuple(vec![
            Type::I32,
            Type::List(Box::new(Type::I32))
        ])
    );

    assert_eq!(
        Type::parse(&mut s_to_stream("[(x, y)]")),
        Type::List(Box::new(Type::Tuple(vec![
            Type::Ident("x".into()),
            Type::Ident("y".into())
        ])))
    );

    eprintln!("Test parsing arrow type");
    assert_eq!(
        Type::parse(&mut s_to_stream("u8 -> u8")),
        Type::Arrow(
            Box::new(Type::U8),
            Box::new(Type::U8)
        )
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("(u8, u8) -> [u8]")),
        Type::Arrow(
            Box::new(Type::Tuple(vec![
                Type::U8,
                Type::U8
            ])),
            Box::new(Type::List(Box::new(Type::U8)))
        )
    );

    eprintln!("Test parsing generic type");
    assert_eq!(
        Type::parse(&mut s_to_stream("list<a>")),
        Type::Generic(
            vec![Type::Ident("a".into())], Box::new(Type::Ident("list".into())))
    );

    assert_eq!(
        Type::parse(&mut s_to_stream("list<a, u8>")),
        Type::Generic(
            vec![
                Type::Ident("a".into()),
                Type::U8
            ], Box::new(Type::Ident("list".into())))
    );
    
}

#[test]
fn test_parse_expression() {
    // Constants
    eprintln!("Test parsing constant expression ");
    assert_eq!(
        Expression::parse(&mut s_to_stream("5")),
        Expression::Num(5)
    );
    assert_eq!(
        Expression::parse(&mut s_to_stream("\"s\"")),
        Expression::Str("s".into())
    );
    
    // Identifier
    eprintln!("Test parsing identifier expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x")),
        Expression::Identifier("x".into())
    );

    // Tuple
    eprintln!("Test parsing tuple expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("(x, 5)")),
        Expression::Tuple(vec![
            Expression::Identifier("x".into()),
            Expression::Num(5),
        ])
    );

    eprintln!("Test parsing tuples of tuples expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("((a, b, c), (1, 2, 3))")),
        Expression::Tuple(vec![
            Expression::Tuple(vec![
                Expression::Identifier("a".into()),
                Expression::Identifier("b".into()),
                Expression::Identifier("c".into()),
            ]),
            Expression::Tuple(vec![
                Expression::Num(1),
                Expression::Num(2),
                Expression::Num(3),
            ])
        ])
    );

    // Let
    eprintln!("Test parsing let expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("let x = 5")),
        Expression::Let(
            Pattern::Var("x".into()),
            Box::new(Expression::Num(5))
        )
    );

    // orexpr
    eprintln!("Test parsing or expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x || y")),
        Expression::Call(
            Box::new(Expression::Identifier("or".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );
    
    eprintln!("Test parsing and expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x && y")),
        Expression::Call(
            Box::new(Expression::Identifier("and".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing bitor expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x | y")),
        Expression::Call(
            Box::new(Expression::Identifier("bitor".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing bitxor expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x ^ y")),
        Expression::Call(
            Box::new(Expression::Identifier("bitxor".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing bitand expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x & y")),
        Expression::Call(
            Box::new(Expression::Identifier("bitand".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing bitand expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x == y")),
        Expression::Call(
            Box::new(Expression::Identifier("eq".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );
    assert_eq!(
        Expression::parse(&mut s_to_stream("x != y")),
        Expression::Call(
            Box::new(Expression::Identifier("neq".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing relative expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x < y")),
        Expression::Call(
            Box::new(Expression::Identifier("lt".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );
    assert_eq!(
        Expression::parse(&mut s_to_stream("x > y")),
        Expression::Call(
            Box::new(Expression::Identifier("gt".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );
    assert_eq!(
        Expression::parse(&mut s_to_stream("x <= y")),
        Expression::Call(
            Box::new(Expression::Identifier("leq".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );
    assert_eq!(
        Expression::parse(&mut s_to_stream("x >= y")),
        Expression::Call(
            Box::new(Expression::Identifier("geq".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing concat expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x::y")),
        Expression::Call(
            Box::new(Expression::Identifier("Cons".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing add expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x + y")),
        Expression::Call(
            Box::new(Expression::Identifier("add".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing mul expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x * y")),
        Expression::Call(
            Box::new(Expression::Identifier("mul".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing pow expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x ** y")),
        Expression::Call(
            Box::new(Expression::Identifier("pow".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing unary expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("!x")),
        Expression::Call(
            Box::new(Expression::Identifier("not".into())),
            vec![Expression::Identifier("x".into())]
        )
    );
    assert_eq!(
        Expression::parse(&mut s_to_stream("~x")),
        Expression::Call(
            Box::new(Expression::Identifier("bitnot".into())),
            vec![Expression::Identifier("x".into())]
        )
    );
    assert_eq!(
        Expression::parse(&mut s_to_stream("-x")),
        Expression::Call(
            Box::new(Expression::Identifier("neg".into())),
            vec![Expression::Identifier("x".into())]
        )
    );

    eprintln!("Test parsing postfix expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x(y)")),
        Expression::Call(
            Box::new(Expression::Identifier("x".into())),
            vec![Expression::Identifier("y".into())]
        )
    );
    assert_eq!(
        Expression::parse(&mut s_to_stream("x.f(y)")),
        Expression::Call(
            Box::new(Expression::Identifier("f".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );
}

#[test]
fn test_parse_pattern() {
    // Unit
    eprintln!("Test parsing unit pattern");
    assert_eq!(
        Pattern::parse(&mut s_to_stream("()")),
        Pattern::Unit
    );

    // Empty List
    eprintln!("Test parsing empty list pattern");
    assert_eq!(
        Pattern::parse(&mut s_to_stream("[]")),
        Pattern::EmptyList
    );

    // Constants
    eprintln!("Test parsing constant pattern");
    assert_eq!(
        Pattern::parse(&mut s_to_stream("7")),
        Pattern::Num(7)
    );
    assert_eq!(
        Pattern::parse(&mut s_to_stream("\"hello\"")),
        Pattern::Str("hello".into())
    );

    // Variable
    eprintln!("Test parsing variable pattern");
    assert_eq!(
        Pattern::parse(&mut s_to_stream("a")),
        Pattern::Var("a".into())
    );

    // Tuple
    eprintln!("Test parsing tuple pattern");
    assert_eq!(
        Pattern::parse(&mut s_to_stream("(a, \"test\", [], 6)")),
        Pattern::Tuple(vec![
            Pattern::Var("a".into()),
            Pattern::Str("test".into()),
            Pattern::EmptyList,
            Pattern::Num(6)
        ])
    );
    assert_eq!(
        Pattern::parse(&mut s_to_stream("(a)")),
        Pattern::Var("a".into()),
    );

    // Constructor
    eprintln!("Test parsing constructor pattern");
    assert_eq!(
        Pattern::parse(&mut s_to_stream("Cons(5, xs)")),
        Pattern::Cons("Cons".into(), Box::new(Pattern::Tuple(vec![
            Pattern::Num(5),
            Pattern::Var("xs".into())
        ])))
    );

    // Complicated
    eprintln!("Test parsing complicated pattern");
    assert_eq!(
        Pattern::parse(&mut s_to_stream("(Cons(a, b), [])")),
        Pattern::Tuple(vec![
            Pattern::Cons("Cons".into(), Box::new(Pattern::Tuple(vec![
                Pattern::Var("a".into()),
                Pattern::Var("b".into())
            ]))),
            Pattern::EmptyList,
        ])
    );
}

#[test]
fn test_parse_arglist() {
    assert_eq!(
        ArgList::parse(&mut s_to_stream("A, B, C")),
        vec![
            Expression::Identifier("A".into()),
            Expression::Identifier("B".into()),
            Expression::Identifier("C".into()),
        ]
    )
}
