use std::collections::HashMap;

use crate::Token;
use crate::lexer::TokenStream;
use crate::lexer::LexemeFeed;
use crate::lexer::Lexeme;
use crate::SteltError;

use crate::parse_tree::{
    ParseTree,
    Trait,
    Impl,
    DataDecl,
    TypeCons,
    Type,
    FunctionDef,
    Expression,
    Pattern,
};

impl ParseTree {
    pub fn parse(t: &mut TokenStream) -> Result<Self, SteltError> {
        let mut me = Self {
            traits: HashMap::new(),
            impls: Vec::new(),
            types: HashMap::new(),
            typedefs: HashMap::new(),
            funcs: HashMap::new(),
            defs: HashMap::new(),
        };

        loop {
            match t.peek() {
                Some(Lexeme {token: Token::Trait, ..}) => {
                    let t = Trait::parse(t)?;
                    me.traits.insert(t.name.clone(), t);
                }
                Some(Lexeme {token: Token::Impl, ..}) => {
                    let i = Impl::parse(t)?;
                    me.impls.push(i);
                }
                Some(Lexeme {token: Token::Type, ..}) => {
                    // Either a typedecl or datadecl
                    t.assert(Token::Type)?;

                    let name = t.ident()?;

                    // generic args for forall type
                    let mut args = Vec::new();
                    if t.consume(Token::LArrow) {

                        let arg = t.ident()?;
                        args.push(arg);

                        while t.consume(Token::Comma) {

                            let arg = t.ident()?;
                            args.push(arg);
                        }

                        t.assert(Token::RArrow)?;
                    }

                    match t.next() {
                        Some(Lexeme {token: Token::Assign, ..}) => {
                            let ty = DataDecl::parse(t, args)?;
                            me.types.insert(name, ty);
                        }
                        Some(Lexeme {token: Token::Colon, ..}) => {
                            let ty = Type::parse(t)?;
                            me.typedefs.insert(name, Type::ForAll(args, Box::new(ty)));
                        }
                        Some(a) => {
                            return Err(SteltError {
                                line: a.line, start: a.start, end: a.end,
                                msg: format!("Expected colon or equals, found {:?}", a.token)
                            })
                        }
                        None => {
                            return Err(SteltError {
                                line: 0, start: 0, end: 0,
                                msg: format!("Expected colon or equals, found EOF")
                            })
                        }
                    }
                }
                Some(Lexeme {token: Token::Def, ..}) => {
                    let name = t.ident()?;

                    let expr = Expression::parse(t)?;
                    me.defs.insert(name, expr);
                }
                Some(Lexeme {token: Token::Ident(_), ..}) => {
                    let name = t.ident()?;
                    let func = FunctionDef::parse(t, name)?;
                    if let Some(f) = me.funcs.get_mut(&func.name) {
                        f.push(func);
                    } else {
                        me.funcs.insert(func.name.clone(), vec![func]);
                    }
                }
                Some(a) => {
                    eprintln!("{me:?}\n");
                    return Err(SteltError {
                        line: a.line, start: a.start, end: a.end,
                        msg: format!("Unexpected token in declaration: {:?}", a.token)
                    })
                }
                None => break
            }
        }

        Ok(me)
    }
}
impl Trait { fn parse(t: &mut TokenStream) -> Result<Self, SteltError> { t.assert(Token::Trait)?;

        let name = t.ident()?;

        t.assert(Token::LArrow)?;

        let var = t.ident()?;

        t.assert(Token::RArrow)?;

        t.assert(Token::LCurly)?;

        let mut types = HashMap::new();
        let mut funcs = HashMap::<String, Vec<FunctionDef>>::new();

        loop {
            match t.next() {
                Some(Lexeme {token: Token::RCurly, ..}) => {
                    break;
                },
                Some(Lexeme {token: Token::Type, ..}) => {
                    // typedecls

                    let name = t.ident()?;

                    t.assert(Token::Colon)?;

                    let ty = Type::parse(t)?;
                    types.insert(name, ty);
                }
                Some(Lexeme {token: Token::Ident(_), ..}) => {
                    let name = t.ident()?;
                    let func = FunctionDef::parse(t, name)?;
                    if let Some(f) = funcs.get_mut(&func.name) {
                        f.push(func);
                    } else {
                        funcs.insert(func.name.clone(), vec![func]);
                    }
                }
                Some(a) => {
                    return Err(SteltError {
                        line: a.line, start: a.start, end: a.end,
                        msg: format!("Unexpected token in trait: {:?}", a.token)
                    })
                }
                None => {
                    return Err(SteltError {
                        line: 0, start: 0, end: 0,
                        msg: format!("Unexpected EOF in trait")
                    })
                }
            }
        }

        Ok(Trait {
            name,
            var,
            types,
            funcs,
        })
    }
}

impl Impl {
    fn parse(t: &mut TokenStream) -> Result<Self, SteltError> {
        t.assert(Token::Impl)?;

        let trait_name = t.ident()?;

        t.assert(Token::For)?;

        let var = Type::parse(t)?;

        t.assert(Token::LCurly)?;

        let mut funcs: HashMap<String, Vec<FunctionDef>> = HashMap::new();

        // Emit impl functions
        while !t.test(Token::RCurly) {
            let name = t.ident()?;
            let func = FunctionDef::parse(t, name)?;

            if let Some(f) = funcs.get_mut(&func.name) {
                f.push(func);
            } else {
                funcs.insert(func.name.clone(), vec![func]);
            }
        }
        t.assert(Token::RCurly)?;

        Ok(Impl {
            trait_name,
            for_type: var,
            funcs
        })
    }
}

impl DataDecl {
    fn parse(t: &mut TokenStream, args: Vec<String>) -> Result<Self, SteltError> {
        let mut cons = Vec::new();
        cons.push(TypeCons::parse(t)?);

        while t.consume(Token::Bar) {
            cons.push(TypeCons::parse(t)?);
        }

        Ok(Self { cons, args })
    }
}

impl TypeCons {
    fn parse(t: &mut TokenStream) -> Result<Self, SteltError> {
        let name = t.ident()?;

        let mut args = Vec::new();
        if t.consume(Token::LParen) {
            args.push(Type::parse(t)?);

            while t.consume(Token::Comma) {
                args.push(Type::parse(t)?);
            }

            t.assert(Token::RParen)?;
        }

        Ok(Self { name, args })
    }
}

impl FunctionDef {
    fn parse(t: &mut TokenStream, name: String) -> Result<Self, SteltError> {
        if !t.test(Token::LParen) {
            // Guaranteed to error
            t.assert(Token::LParen)?;
        }

        let args = Pattern::parse(t)?;

        t.assert(Token::Assign)?;

        let body = Expression::parse(t)?;

        return Ok(FunctionDef {name, args, body})
    }
}

impl Type {
    fn parse(t: &mut TokenStream) -> Result<Self, SteltError> {
        let cont = Self::parse_tuple(t)?;

        if t.consume(Token::Arrow) {
            let end = Self::parse_tuple(t)?;

            Ok(Self::Arrow(Box::new(cont), Box::new(end)))
        } else {
            Ok(cont)
        }
    }

    fn parse_tuple(t: &mut TokenStream) -> Result<Self, SteltError> {
        if t.consume(Token::LParen) {
            if t.consume(Token::RParen) {
                // Not a tuple, an empty type
                return Ok(Self::Unit);
            }

            let mut inner = vec![Self::parse(t)?];

            // Parse comma separated fields
            while t.consume(Token::Comma) {
                inner.push(Self::parse(t)?);
            }

            t.assert(Token::RParen)?;
            
            Ok(Self::Tuple(inner))
        } else {
            Ok(Self::parse_list(t)?)
        }
    }

    fn parse_list(t: &mut TokenStream) -> Result<Self, SteltError> {
        if t.consume(Token::LBrace) {
            let inner = Self::parse(t)?;

            t.assert(Token::RBrace)?;

            Ok(Self::List(Box::new(inner)))
        } else {
            Ok(Self::parse_generic(t)?)
        }
    }

    fn parse_generic(t: &mut TokenStream) -> Result<Self, SteltError> {
        let base = Self::parse_base(t)?;

        if t.consume(Token::LArrow) {
            let mut vars = Vec::new();
            vars.push(Self::parse(t)?);

            while t.consume(Token::Comma) {
                vars.push(Self::parse(t)?);
            }

            t.assert(Token::RArrow)?;
            
            Ok(Self::Generic(vars, Box::new(base)))
        } else {
            Ok(base)
        }
    }

    fn parse_base(t: &mut TokenStream) -> Result<Self, SteltError> {
        Ok(match t.next() {
            Some(Lexeme {token: Token::Ident(i), ..}) => Self::Ident(i),
            Some(Lexeme {token: Token::U8, ..}) => Self::U8,
            Some(Lexeme {token: Token::U16, ..}) => Self::U16,
            Some(Lexeme {token: Token::U32, ..}) => Self::U32,
            Some(Lexeme {token: Token::U64, ..}) => Self::U64,
            Some(Lexeme {token: Token::I8, ..}) => Self::I8,
            Some(Lexeme {token: Token::I16, ..}) => Self::I16,
            Some(Lexeme {token: Token::I32, ..}) => Self::I32,
            Some(Lexeme {token: Token::I64, ..}) => Self::I64,
            Some(Lexeme {token: Token::Str, ..}) => Self::Str,
            Some(a) => {
                return Err(SteltError {
                    line: a.line, start: a.start, end: a.end,
                    msg: format!("Unexpected token in type: {:?}", a.token)
                })
            }
            None => {
                return Err(SteltError {
                    line: 0, start: 0, end: 0,
                    msg: format!("Unexpected EOF in type")
                })
            }
        })
    }
}


impl Expression {
    pub fn parse_list_scoped(t: &mut TokenStream) -> Result<Vec<Expression>, SteltError> {
        let mut exprs = vec![];
        while !t.test(Token::RCurly) {
            let e = match Self::parse(t)? {
                Self::Let(pat, val, _) => {
                    let rest = Self::parse_list_scoped(t)?;
                    let body = match rest.len() {
                        0 => Expression::Unit,
                        1 => rest.into_iter().next().unwrap(),
                        _ => Self::ExprList(rest)
                    };

                    Self::Let(pat, val, Box::new(body))
                }
                a => a
            };

            exprs.push(e);
        }

        Ok(exprs)
    }

    pub fn parse_list(t: &mut TokenStream) -> Result<Self, SteltError> {
        t.assert(Token::LCurly)?;
        let exprs = Self::parse_list_scoped(t)?;
        t.assert(Token::RCurly)?;

        match exprs.len() {
            0 => Ok(Expression::Unit),
            1 => Ok(exprs.into_iter().next().unwrap()),
            _ => Ok(Self::ExprList(exprs))
        }
    }

    pub fn parse(t: &mut TokenStream) -> Result<Self, SteltError> {
        if t.test(Token::LCurly) {
            Self::parse_list(t)
        } else if t.consume(Token::Let) {
            let pat = Pattern::parse(t)?;

            t.assert(Token::Assign)?;

            Ok(Self::Let(pat, Box::new(Self::lambda(t)?), Box::new(Self::Unit)))
        } else if t.consume(Token::If) {
            let cond = Self::parse(t)?;


            let then = Self::parse_list(t)?;

            t.assert(Token::Else)?;

            let else_ = Self::parse_list(t)?;

            Ok(Self::If(Box::new(cond), Box::new(then), Box::new(else_)))
        } else if t.consume(Token::Match) {
            let match_ = Self::parse(t)?;

            t.assert(Token::LCurly)?;

            let pat = Pattern::parse(t)?;
            t.assert(Token::Colon)?;
            let e = Self::parse(t)?;

            let mut cases = vec![(pat, e)];

            while t.consume(Token::Comma) {
                let pat = Pattern::parse(t)?;
                t.assert(Token::Colon)?;
                let e = Self::parse(t)?;
                cases.push((pat, e));
            }

            t.assert(Token::RCurly)?;

            Ok(Self::Match(Box::new(match_), cases))
        } else {
            Ok(Self::lambda(t)?)
        }
    }

    pub fn lambda(t: &mut TokenStream) -> Result<Self, SteltError> {
        let tup = Self::tuple(t)?;

        if t.consume(Token::Arrow) {
            let pat = tup.to_lambda_pattern();
            let e = Self::parse(t)?;
            Ok(Self::Lambda(pat, Box::new(e)))
        } else {
            Ok(tup)
        }
    }

    pub fn tuple(t: &mut TokenStream) -> Result<Self, SteltError> {
        if t.consume(Token::LParen) {
            if t.consume(Token::RParen) {
                return Ok(Self::Unit);
            }

            let mut es = Vec::new();
            es.push(Self::parse(t)?);

            while t.consume(Token::Comma) {
                es.push(Self::parse(t)?);
            }

            t.assert(Token::RParen)?;

            let e = if es.len() == 1 {
                es.into_iter().next().unwrap()
            } else {
                Self::Tuple(es)
            };

            // allow postfix expressions on tuples
            Self::postfix_post(t, e)
        } else {
            Self::orexpr(t)
        }
    }

    pub fn orexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let and = Self::andexpr(t)?;

        if t.consume(Token::Or) {
            let end = Self::orexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("or".into())),
                vec![and, end]
            ))
        } else {
            Ok(and)
        }
    }

    fn andexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let bitor = Self::bitorexpr(t)?;

        if t.consume(Token::And) {
            let end = Self::andexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("and".into())),
                vec![bitor, end]
            ))
        } else {
            Ok(bitor)
        }
    }

    fn bitorexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let xor = Self::bitxorexpr(t)?;

        if t.consume(Token::Bar) {
            let end = Self::bitorexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("bitor".into())),
                vec![xor, end]
            ))
        } else {
            Ok(xor)
        }
    }

    fn bitxorexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let and = Self::bitandexpr(t)?;

        if t.consume(Token::BitXor) {
            let end = Self::bitxorexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("bitxor".into())),
                vec![and, end]
            ))
        } else {
            Ok(and)
        }
    }

    fn bitandexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let eq = Self::eqexpr(t)?;

        if t.consume(Token::BitAnd) {
            let end = Self::bitandexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("bitand".into())),
                vec![eq, end]
            ))
        } else {
            Ok(eq)
        }
    }

    fn eqexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let rel = Self::relexpr(t)?;

        if t.consume(Token::NotEqual) {
            let end = Self::eqexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("neq".into())),
                vec![rel, end]
            ))
        } else if t.consume(Token::Equal) {
            let end = Self::eqexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("eq".into())),
                vec![rel, end]
            ))
        } else {
            Ok(rel)
        }
    }

    fn relexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let conc = Self::concexpr(t)?;

        if t.consume(Token::LArrow) {
            let end = Self::relexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("lt".into())),
                vec![conc, end]
            ))
        }
        else if t.consume(Token::RArrow) {
            let end = Self::relexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("gt".into())),
                vec![conc, end]
            ))
        }
        else if t.consume(Token::LTE) {
            let end = Self::relexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("leq".into())),
                vec![conc, end]
            ))
        }
        else if t.consume(Token::GTE) {
            let end = Self::relexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("geq".into())),
                vec![conc, end]
            ))
        }
        else {
            Ok(conc)
        }
    }

    fn concexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let add = Self::addexpr(t)?;

        if t.consume(Token::Concat) {
            let end = Self::concexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("Cons".into())),
                vec![add, end]
            ))
        } else {
            Ok(add)
        }
    }

    fn addexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let mul = Self::mulexpr(t)?;

        if t.consume(Token::Plus) {
            let end = Self::addexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("add".into())),
                vec![mul, end]
            ))
        } else if t.consume(Token::Sub) {
            let end = Self::addexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("sub".into())),
                vec![mul, end]
            ))
        } else {
            Ok(mul)
        }
    }

    fn mulexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let pow = Self::powexpr(t)?;

        if t.consume(Token::Mul) {
            let end = Self::mulexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("mul".into())),
                vec![pow, end]
            ))
        } else if t.consume(Token::Div) {
            let end = Self::mulexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("div".into())),
                vec![pow, end]
            ))
        } else if t.consume(Token::Mod) {
            let end = Self::mulexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("mod".into())),
                vec![pow, end]
            ))
        } else {
            Ok(pow)
        }
    }

    fn powexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let unary = Self::unary(t)?;

        if t.consume(Token::Pow) {
            let end = Self::powexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("pow".into())),
                vec![unary, end]
            ))
        } else {
            Ok(unary)
        }
    }

    fn unary(t: &mut TokenStream) -> Result<Self, SteltError> {
        if t.consume(Token::Not) {
            let un = Self::unary(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("not".into())),
                vec![un]
            ))
        } else if t.consume(Token::BitNot) {
            let un = Self::unary(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("bitnot".into())),
                vec![un]
            ))
        } else if t.consume(Token::Sub) {
            let un = Self::unary(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("neg".into())),
                vec![un]
            ))
        } else {
            Ok(Self::postfix(t)?)
        }
    }

    fn postfix(t: &mut TokenStream) -> Result<Self, SteltError> {
        let primary = Self::primary(t)?;
        Self::postfix_post(t, primary)
    }

    fn postfix_post(t: &mut TokenStream, primary: Expression) -> Result<Self, SteltError> {
        if t.consume(Token::LParen) {
                let al = if t.test(Token::RParen) {
                    vec![]
                } else {
                    ArgList::parse(t)?
                };

                t.assert(Token::RParen)?;

                Ok(Self::Call(Box::new(primary), al))
        } else if t.consume(Token::Dot) {
                let call = Self::postfix(t)?;
                match call {
                    Self::Call(f, mut args) => {
                        args.insert(0, primary);
                        Ok(Self::Call(f, args))
                    }
                    _ => {panic!("expected call")}
                }

        } else if t.consume(Token::Question) {
            let then = Expression::parse(t)?;

            t.assert(Token::Colon)?;

            let else_ = Expression::parse(t)?;

            Ok(Self::If(Box::new(primary), Box::new(then), Box::new(else_)))
        } else {
            Ok(primary)
        }

    }

    fn primary(t: &mut TokenStream) -> Result<Self, SteltError> {
        match t.next() {
            Some(Lexeme {token: Token::String(s), ..}) => {
                Ok(Self::Str(s))
            }
            Some(Lexeme {token: Token::Num(n), ..}) => {
                Ok(Self::Num(n))
            }
            Some(Lexeme {token: Token::Ident(i), ..}) => {
                Ok(Self::Identifier(i.clone()))
            }
            Some(Lexeme {token: Token::LParen, ..}) => {
                let e = Expression::parse(t)?;
                t.assert(Token::RParen)?;
                Ok(e)
            }
            Some(Lexeme { token: Token::LBrace, ..}) => {
                t.assert(Token::RBrace)?;
                Ok(Self::EmptyList)
            }
            Some(a) => {
                //panic!("PrimaryExpr: Expected identifier, constant, or expression, found: {:?}", a);
                Err(SteltError {
                    line: a.line, start: a.start, end: a.start+1, msg: format!("Expected expression, found {:?}", a.token)
                })
            }
            None => {
                Err(SteltError {
                    line: 0, start: 0, end: 0, msg: "Expected expression".into() })
            }
        }
    }

    fn to_lambda_pattern(&self) -> Pattern {
        match self {
            Self::Identifier(s) => Pattern::Var(s.clone()),
            Self::Tuple(es) => Pattern::Tuple(es.iter().map(|e| e.to_lambda_pattern()).collect()),
            _ => panic!("ahh")
        }
    }
}


impl Pattern {
    fn parse(t: &mut TokenStream) -> Result<Pattern, SteltError> {
        if t.consume(Token::LParen) {
            // We are either the unit type or the tuple type

            if t.consume(Token::RParen) {
                return Ok(Pattern::Unit);
            }

            let mut pats = Vec::new();
            pats.push(Pattern::parse_conc(t)?);

            while t.consume(Token::Comma) {
                pats.push(Pattern::parse_conc(t)?);
            }

            t.assert(Token::RParen)?;

            if pats.len() == 1 {
                Ok(pats.into_iter().next().unwrap())
            } else {
                Ok(Pattern::Tuple(pats))
            }
        } else {
            Pattern::parse_conc(t)
        }
    }

    fn parse_conc(t: &mut TokenStream) -> Result<Pattern, SteltError> {
        let a = Self::parse_base(t)?;

        if t.consume(Token::Concat) {
            let b = Self::parse_base(t)?;

            Ok(Self::Cons(
                "Cons".into(),
                Box::new(Pattern::Tuple(vec![a, b]))
            ))
        } else {
            Ok(a)
        }
    }

    fn parse_base(t: &mut TokenStream) -> Result<Pattern, SteltError> {
        match t.next() {
            Some(Lexeme {token: Token::LBrace, ..}) => {
                t.assert(Token::RBrace)?;
                Ok(Pattern::EmptyList)
            }
            Some(Lexeme {token: Token::Num(n), ..}) => {
                Ok(Pattern::Num(n))
            }
            Some(Lexeme {token: Token::String(s), ..}) => {
                Ok(Pattern::Str(s))
            }
            Some(Lexeme {token: Token::Ident(i), ..}) => {
                // either variable or constructor...
                if t.test(Token::LParen) {
                    let pat = Pattern::parse(t)?;
                    Ok(Pattern::Cons(i, Box::new(pat)))
                } else {
                    Ok(Pattern::Var(i))
                }
            }
            _ => panic!("unexpected token")
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct ArgList;
impl ArgList {
    fn parse(t: &mut TokenStream) -> Result<Vec<Expression>, SteltError> {
        let mut exprs = Vec::new();
        exprs.push(Expression::parse(t)?);

        while t.consume(Token::Comma) {
            exprs.push(Expression::parse(t)?);
        }

        Ok(exprs)
    }
}

// Tests
#[allow(dead_code)]
fn s_to_stream(s: &str) -> TokenStream {
    use crate::Lexer;
    let mut l = Lexer::default();
    l.lex(s).unwrap()
}

#[test]
fn test_parse_type() {
    eprintln!("Test parsing builtin type");
    assert_eq!(
        Type::parse(&mut s_to_stream("u8")).unwrap(),
        Type::U8
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("u16")).unwrap(),
        Type::U16
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("u32")).unwrap(),
        Type::U32
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("u64")).unwrap(),
        Type::U64
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("i8")).unwrap(),
        Type::I8
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("i16")).unwrap(),
        Type::I16
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("i32")).unwrap(),
        Type::I32
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("i64")).unwrap(),
        Type::I64
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("()")).unwrap(),
        Type::Unit
    );

    eprintln!("Test parsing list type");
    assert_eq!(
        Type::parse(&mut s_to_stream("[i64]")).unwrap(),
        Type::List(Box::new(Type::I64))
    );

    eprintln!("Test parsing identifier type");
    assert_eq!(
        Type::parse(&mut s_to_stream("x")).unwrap(),
        Type::Ident("x".to_string())
    );

    eprintln!("Test parsing tuple type");
    assert_eq!(
        Type::parse(&mut s_to_stream("(x, y)")).unwrap(),
        Type::Tuple(vec![
            Type::Ident("x".into()),
            Type::Ident("y".into())
        ])
    );

    assert_eq!(
        Type::parse(&mut s_to_stream("(i32, [i32])")).unwrap(),
        Type::Tuple(vec![
            Type::I32,
            Type::List(Box::new(Type::I32))
        ])
    );

    assert_eq!(
        Type::parse(&mut s_to_stream("[(x, y)]")).unwrap(),
        Type::List(Box::new(Type::Tuple(vec![
            Type::Ident("x".into()),
            Type::Ident("y".into())
        ])))
    );

    eprintln!("Test parsing arrow type");
    assert_eq!(
        Type::parse(&mut s_to_stream("u8 -> u8")).unwrap(),
        Type::Arrow(
            Box::new(Type::U8),
            Box::new(Type::U8)
        )
    );
    assert_eq!(
        Type::parse(&mut s_to_stream("(u8, u8) -> [u8]")).unwrap(),
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
        Type::parse(&mut s_to_stream("list<a>")).unwrap(),
        Type::Generic(
            vec![Type::Ident("a".into())], Box::new(Type::Ident("list".into())))
    );

    assert_eq!(
        Type::parse(&mut s_to_stream("list<a, u8>")).unwrap(),
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
        Expression::parse(&mut s_to_stream("5")).unwrap(),
        Expression::Num(5)
    );
    assert_eq!(
        Expression::parse(&mut s_to_stream("\"s\"")).unwrap(),
        Expression::Str("s".into())
    );
    
    // Identifier
    eprintln!("Test parsing identifier expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x")).unwrap(),
        Expression::Identifier("x".into())
    );

    // Unit
    eprintln!("Test parsing unit expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("()")).unwrap(),
        Expression::Unit
    );

    // Tuple
    eprintln!("Test parsing tuple expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("(x, 5)")).unwrap(),
        Expression::Tuple(vec![
            Expression::Identifier("x".into()),
            Expression::Num(5),
        ])
    );

    eprintln!("Test parsing tuples of tuples expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("((a, b, c), (1, 2, 3))")).unwrap(),
        Expression::Tuple(vec![
            Expression::Tuple(vec![
                Expression::Identifier("a".into()),
                Expression::Identifier("b".into()), Expression::Identifier("c".into()), ]), Expression::Tuple(vec![
                Expression::Num(1),
                Expression::Num(2),
                Expression::Num(3),
            ])
        ])
    );

    // Test parsing lambda expression
    eprintln!("Test parsing lambda expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("(x, y) -> x+y")).unwrap(),
        Expression::Lambda(
            Pattern::Tuple(vec![Pattern::Var("x".into()), Pattern::Var("y".into())]),
            Box::new(Expression::Call(Box::new(Expression::Identifier("add".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]))
        )
    );

    // Test inline calling of lambda expression
    eprintln!("Test calling lambda expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("(x -> x)(5)")).unwrap(),
        Expression::Call(
            Box::new(
                Expression::Lambda(
                    Pattern::Var("x".into()),
                    Box::new(Expression::Identifier("x".into())),
                )
            ),
            vec![Expression::Num(5)]
        )
    );

    // Let
    eprintln!("Test parsing let expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("let x = 5")).unwrap(),
        Expression::Let(
            Pattern::Var("x".into()),
            Box::new(Expression::Num(5)),
            Box::new(Expression::Unit)
        )
    );

    // If
    eprintln!("Test parsing if expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("if a { x } else { y }")).unwrap(),
        Expression::If(
            Box::new(Expression::Identifier("a".into())),
            Box::new(Expression::Identifier("x".into())),
            Box::new(Expression::Identifier("y".into()))
        )
    );

    // Match
    eprintln!("Test parsing match expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("match a { a: a, Cons(b): b }")).unwrap(),
        Expression::Match(
            Box::new(Expression::Identifier("a".into())),
            vec![
                (Pattern::Var("a".into()), Expression::Identifier("a".into())),
                (Pattern::Cons("Cons".into(), Box::new(Pattern::Var("b".into()))), Expression::Identifier("b".into()))
            ])
    );

    // Ternary operator BABY
    assert_eq!(
        Expression::parse(&mut s_to_stream("a? x: y")).unwrap(),
        Expression::If(
            Box::new(Expression::Identifier("a".into())),
            Box::new(Expression::Identifier("x".into())),
            Box::new(Expression::Identifier("y".into()))
        )
    );

    // Match expression

    // orexpr
    eprintln!("Test parsing or expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x || y")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("or".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );
    
    eprintln!("Test parsing and expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x && y")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("and".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing bitor expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x | y")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("bitor".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing bitxor expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x ^ y")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("bitxor".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing bitand expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x & y")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("bitand".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing bitand expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x == y")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("eq".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );
    assert_eq!(
        Expression::parse(&mut s_to_stream("x != y")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("neq".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing relative expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x < y")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("lt".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );
    assert_eq!(
        Expression::parse(&mut s_to_stream("x > y")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("gt".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );
    assert_eq!(
        Expression::parse(&mut s_to_stream("x <= y")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("leq".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );
    assert_eq!(
        Expression::parse(&mut s_to_stream("x >= y")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("geq".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing concat expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x::y")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("Cons".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing add expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x + y")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("add".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing mul expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x * y")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("mul".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing pow expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x ** y")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("pow".into())),
            vec![Expression::Identifier("x".into()), Expression::Identifier("y".into())]
        )
    );

    eprintln!("Test parsing unary expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("!x")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("not".into())),
            vec![Expression::Identifier("x".into())]
        )
    );
    assert_eq!(
        Expression::parse(&mut s_to_stream("~x")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("bitnot".into())),
            vec![Expression::Identifier("x".into())]
        )
    );
    assert_eq!(
        Expression::parse(&mut s_to_stream("-x")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("neg".into())),
            vec![Expression::Identifier("x".into())]
        )
    );

    eprintln!("Test parsing postfix expression");
    assert_eq!(
        Expression::parse(&mut s_to_stream("x(y)")).unwrap(),
        Expression::Call(
            Box::new(Expression::Identifier("x".into())),
            vec![Expression::Identifier("y".into())]
        )
    );
    assert_eq!(
        Expression::parse(&mut s_to_stream("x.f(y)")).unwrap(),
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
        Pattern::parse(&mut s_to_stream("()")).unwrap(),
        Pattern::Unit
    );

    // Empty List
    eprintln!("Test parsing empty list pattern");
    assert_eq!(
        Pattern::parse(&mut s_to_stream("[]")).unwrap(),
        Pattern::EmptyList
    );

    // Constants
    eprintln!("Test parsing constant pattern");
    assert_eq!(
        Pattern::parse(&mut s_to_stream("7")).unwrap(),
        Pattern::Num(7)
    );
    assert_eq!(
        Pattern::parse(&mut s_to_stream("\"hello\"")).unwrap(),
        Pattern::Str("hello".into())
    );

    // Variable
    eprintln!("Test parsing variable pattern");
    assert_eq!(
        Pattern::parse(&mut s_to_stream("a")).unwrap(),
        Pattern::Var("a".into())
    );

    // Tuple
    eprintln!("Test parsing tuple pattern");
    assert_eq!(
        Pattern::parse(&mut s_to_stream("(a, \"test\", [], 6)")).unwrap(),
        Pattern::Tuple(vec![
            Pattern::Var("a".into()),
            Pattern::Str("test".into()),
            Pattern::EmptyList,
            Pattern::Num(6)
        ])
    );
    assert_eq!(
        Pattern::parse(&mut s_to_stream("(a)")).unwrap(),
        Pattern::Var("a".into()),
    );

    // Constructor
    eprintln!("Test parsing constructor pattern");
    assert_eq!(
        Pattern::parse(&mut s_to_stream("Cons(5, xs)")).unwrap(),
        Pattern::Cons("Cons".into(), Box::new(Pattern::Tuple(vec![
            Pattern::Num(5),
            Pattern::Var("xs".into())
        ])))
    );

    // Complicated
    eprintln!("Test parsing complicated pattern");
    assert_eq!(
        Pattern::parse(&mut s_to_stream("(Cons(a, b), [])")).unwrap(),
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
        ArgList::parse(&mut s_to_stream("A, B, C")).unwrap(),
        vec![
            Expression::Identifier("A".into()),
            Expression::Identifier("B".into()),
            Expression::Identifier("C".into()),
        ]
    )
}
