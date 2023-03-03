use crate::lexer::TokenStream;
use crate::Token;

#[derive(Debug, PartialEq, Eq)]
pub struct Program(Vec<Declaration>);

impl Program {
    pub fn parse(t: &mut TokenStream) -> Self {
        let mut decls = Vec::new();
        while *t.peek() != Token::EOF {
            decls.push(Declaration::parse(t));
        }

        Self(decls)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Declaration {
    Def(String, Expression),
    Type(TypeDeclaration),
    Func(String, Vec<Expression>, Vec<Expression>),
}

impl Declaration {
    pub fn parse(t: &mut TokenStream) -> Self {
        match t.peek().clone() {
            Token::Def => {
                Self::parse_def(t)
            }
            Token::Type => {
                Self::parse_type(t)
            }
            Token::Ident(_) => {
                Self::parse_func(t)
            }
            _ => {
                panic!("Invalid Starting Token")
            }
        }
    }

    fn parse_def(t: &mut TokenStream) -> Self {
        assert_eq!(*t.peek(), Token::Def);
        t.adv();

        if let Token::Ident(i) = t.peek().clone() {
            t.adv();

            assert_eq!(*t.peek(), Token::Assign);
            t.adv();
            
            let e = Expression::parse(t);
            return Declaration::Def(i.clone(), e);
        }

        panic!("Failed to parse def declaration");
    }

    fn parse_type(t: &mut TokenStream) -> Self {
        let tl = TypeDeclaration::parse(t);
        Declaration::Type(tl)
    }

    fn parse_func(t: &mut TokenStream) -> Self {
        if let Token::Ident(name) = t.peek().clone() {
            t.adv();

            assert_eq!(*t.peek(), Token::LParen);
            t.adv();
            
            let args = if *t.peek() == Token::RParen {
                vec![]
            } else {
                ArgList::parse(t).0
            };

            assert_eq!(*t.peek(), Token::RParen);
            t.adv();

            assert_eq!(*t.peek(), Token::Assign);
            t.adv();
            
            let mut exprs = Vec::new();
            if *t.peek() == Token::LCurly {
                t.adv();

                while *t.peek() != Token::RCurly {
                    exprs.push(Expression::parse(t));
                }

                assert_eq!(*t.peek(), Token::RCurly);
                t.adv();
            } else {
                exprs.push(Expression::parse(t));
            }

            return Self::Func(name, args, exprs)
        }

        panic!("Failed to parse func declaration");
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum TypeDeclaration {
    Simple(String),
    Union(String, Vec<TypeDeclaration>),
    Named(String, Box<Field>),
}

impl TypeDeclaration {
    fn parse(t: &mut TokenStream) -> Self {
        assert_eq!(*t.peek(), Token::Type);
        t.adv();

        let name = if let Token::Ident(i) = t.peek().clone() {
            i
        } else {
            panic!("Expected identifier");
        };
        t.adv();

        if *t.peek() == Token::LParen {
            t.adv();

            let out = if *t.peek() == Token::Type {
                // Union of type declarations
                Self::parse_union(t, name)
            } else {
                // Sequence of fields
                Self::parse_field(t, name)
            };

            assert_eq!(*t.peek(), Token::RParen);
            t.adv();

            out
        } else {
            Self::Simple(name)
        }
    }

    fn parse_union(t: &mut TokenStream, name: String) -> Self {
        let mut types = Vec::new();

        types.push(TypeDeclaration::parse(t));

        while *t.peek() == Token::Bar {
            t.adv();

            types.push(TypeDeclaration::parse(t));
        }

        Self::Union(name, types)
    }

    fn parse_field(t: &mut TokenStream, name: String) -> Self {
        let field = Field::parse(t);
        Self::Named(name, Box::new(field))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Field {
    Seqn(Box<Field>, Box<Field>),
    Func(Box<Field>, Box<Field>),
    Named(String, Box<Field>),
    Tuple(Box<Field>),
    List(Box<Field>),
    Ident(String),

    // Builtins
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    Str,
}

impl Field {
    fn parse(t: &mut TokenStream) -> Self {
        let func = Self::parse_func(t);

        if *t.peek() == Token::Comma {
            t.adv();
            let end = Self::parse(t);

            Self::Seqn(Box::new(func), Box::new(end))
        } else {
            func
        }
    }

    fn parse_func(t: &mut TokenStream) -> Self {
        let named = Self::parse_named(t);

        if *t.peek() == Token::Arrow {
            t.adv();
            let end = Self::parse_named(t);

            Self::Func(Box::new(named), Box::new(end))
        } else {
            named
        }
    }

    fn parse_named(t: &mut TokenStream) -> Self {
        // This one's a bit complicated...
        // If I see an identifier, it must be followed by a:
        // - builtin
        // - identifier
        // - tuple
        // - list
        // If it is followed by ->, this is just an identifier for the name, that's it.

        if let Token::Ident(name) = t.peek().clone() {
            t.adv();

            match *t.peek() {
                // Safe to keep parsing named
                Token::U8 
                | Token::U16
                | Token::U32
                | Token::U64
                | Token::I8
                | Token::I16
                | Token::I32
                | Token::I64
                | Token::Ident(_)
                | Token::LParen
                | Token::LBrace => {
                    let end = Self::parse_tuple(t);
                    Self::Named(name, Box::new(end))
                }
                // Bypass named
                _ => {
                    Self::Ident(name)
                }
            }
        } else {
            Self::parse_tuple(t)
        }
    }

    fn parse_tuple(t: &mut TokenStream) -> Self {
        if *t.peek() == Token::LParen {
            t.adv();

            let inner = Self::parse(t);

            assert_eq!(*t.peek(), Token::RParen);
            t.adv();
            
            Self::Tuple(Box::new(inner))
        } else {
            Self::parse_list(t)
        }
    }

    fn parse_list(t: &mut TokenStream) -> Self {
        if *t.peek() == Token::LBrace {
            t.adv();

            let inner = Self::parse_func(t);

            assert_eq!(*t.peek(), Token::RBrace);
            t.adv();

            Self::List(Box::new(inner))
        } else {
            Self::parse_base(t)
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
            _ => { panic!("parse_base: Unexpected token") }
        };

        t.adv();
        out
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Expression {
    Concat(Box<Expression>, Box<Expression>),
    Or(Box<Expression>, Box<Expression>),
    And(Box<Expression>, Box<Expression>),
    BitOr(Box<Expression>, Box<Expression>),
    BitXor(Box<Expression>, Box<Expression>),
    BitAnd(Box<Expression>, Box<Expression>),

    Equal(Box<Expression>, Box<Expression>),
    NotEqual(Box<Expression>, Box<Expression>),

    LT(Box<Expression>, Box<Expression>),
    GT(Box<Expression>, Box<Expression>),
    LTE(Box<Expression>, Box<Expression>),
    GTE(Box<Expression>, Box<Expression>),

    Add(Box<Expression>, Box<Expression>),
    Sub(Box<Expression>, Box<Expression>),

    Mul(Box<Expression>, Box<Expression>),
    Div(Box<Expression>, Box<Expression>),
    Mod(Box<Expression>, Box<Expression>),

    Pow(Box<Expression>, Box<Expression>),

    Not(Box<Expression>),
    BitNot(Box<Expression>),
    Pos(Box<Expression>),
    Neg(Box<Expression>),

    Call(Box<Expression>, Box<ArgList>),
    Field(Box<Expression>, Box<Expression>),

    Num(u64),
    String(String),
    Identifier(String)
}

impl Expression {
    pub fn parse(t: &mut TokenStream) -> Self {
        let and = Self::andexpr(t);

        if *t.peek() == Token::Or {
            t.adv();
            let end = Self::parse(t);
            Self::Or(Box::new(and), Box::new(end))
        } else {
            and
        }
    }

    fn andexpr(t: &mut TokenStream) -> Self {
        let bitor = Self::bitorexpr(t);

        if *t.peek() == Token::And {
            t.adv();
            let end = Self::andexpr(t);
            Self::And(Box::new(bitor), Box::new(end))
        } else {
            bitor
        }
    }

    fn bitorexpr(t: &mut TokenStream) -> Self {
        let xor = Self::bitxorexpr(t);

        if *t.peek() == Token::Bar {
            t.adv();
            let end = Self::bitorexpr(t);
            Self::BitOr(Box::new(xor), Box::new(end))
        } else {
            xor
        }
    }

    fn bitxorexpr(t: &mut TokenStream) -> Self {
        let and = Self::bitandexpr(t);

        if *t.peek() == Token::BitXor {
            t.adv();
            let end = Self::bitxorexpr(t);
            Self::BitXor(Box::new(and), Box::new(end))
        } else {
            and
        }
    }

    fn bitandexpr(t: &mut TokenStream) -> Self {
        let eq = Self::eqexpr(t);

        if *t.peek() == Token::BitAnd {
            t.adv();
            let end = Self::bitandexpr(t);
            Self::BitAnd(Box::new(eq), Box::new(end))
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
                Expression::NotEqual(Box::new(rel), Box::new(end))
            }
            Token::Equal => {
                t.adv();
                let end = Self::eqexpr(t);
                Expression::Equal(Box::new(rel), Box::new(end))
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
                Expression::LT(Box::new(conc), Box::new(end))
            }
            Token::RArrow => {
                t.adv();
                let end = Self::relexpr(t);
                Expression::GT(Box::new(conc), Box::new(end))
            }
            Token::LTE => {
                t.adv();
                let end = Self::relexpr(t);
                Expression::LTE(Box::new(conc), Box::new(end))
            }
            Token::GTE => {
                t.adv();
                let end = Self::relexpr(t);
                Expression::GTE(Box::new(conc), Box::new(end))
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
            Expression::Concat(Box::new(add), Box::new(end))
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
                Self::Add(Box::new(mul), Box::new(end))
            }
            Token::Sub => {
                t.adv();
                let end = Self::addexpr(t);
                Self::Sub(Box::new(mul), Box::new(end))
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
                Self::Mul(Box::new(pow), Box::new(end))
            }
            Token::Div => {
                t.adv();
                let end = Self::mulexpr(t);
                Self::Div(Box::new(pow), Box::new(end))
            }
            Token::Mod => {
                t.adv();
                let end = Self::mulexpr(t);
                Self::Mod(Box::new(pow), Box::new(end))
            }
            _ => { pow }
        }
    }

    fn powexpr(t: &mut TokenStream) -> Self {
        let unary = Self::unary(t);

        if *t.peek() == Token::Pow {
            t.adv();
            let end = Self::powexpr(t);
            Self::Pow(Box::new(unary), Box::new(end))
        } else {
            unary
        }
    }

    fn unary(t: &mut TokenStream) -> Self {
        match *t.peek() {
            Token::Not => {
                t.adv();
                let un = Self::unary(t);
                Self::Not(Box::new(un))
            }
            Token::BitNot => {
                t.adv();
                let un = Self::unary(t);
                Self::BitNot(Box::new(un))
            }
            Token::Plus => {
                t.adv();
                let un = Self::unary(t);
                Self::Pos(Box::new(un))
            }
            Token::Sub => {
                t.adv();
                let un = Self::unary(t);
                Self::Neg(Box::new(un))
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
                    ArgList(vec![])
                } else {
                    ArgList::parse(t)
                };

                assert_eq!(*t.peek(), Token::RParen);
                t.adv();

                Self::Call(Box::new(primary), Box::new(al))
            }
            Token::Dot => {
                t.adv();
                if let Token::Ident(i) = t.peek().clone() {
                    Self::Field(Box::new(primary), Box::new(Self::Identifier(i)))
                } else {
                    panic!("Postfix: Expected identifier");
                }
            }
            _ => primary
        }
    }

    fn primary(t: &mut TokenStream) -> Self {
        match t.peek().clone() {
            Token::String(s) => {
                t.adv();
                Self::String(s.clone())
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
            _ => {
                panic!("PrimaryExpr: Expected identifier, constant, or expression")
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct ArgList(Vec<Expression>);
impl ArgList {
    fn parse(t: &mut TokenStream) -> Self {
        let mut exprs = Vec::new();
        exprs.push(Expression::parse(t));

        while *t.peek() == Token::Comma {
            t.adv();
            exprs.push(Expression::parse(t));
        }

        Self(exprs)
    }
}
