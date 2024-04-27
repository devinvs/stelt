use std::collections::HashMap;
use std::collections::VecDeque;

use lazy_static::lazy_static;

lazy_static! {
    pub static ref MAP: HashMap<&'static str, Token> = {
        let mut m = HashMap::new();

        // Keywords
        m.insert("import", Token::Import);
        m.insert("from", Token::From);
        m.insert("as", Token::As);
        m.insert("alias", Token::Alias);
        m.insert("pub", Token::Pub);
        m.insert("extern", Token::Extern);
        m.insert("type", Token::Type);
        m.insert("typefn", Token::Typefn);
        m.insert("impl", Token::Impl);
        m.insert("for", Token::For);
        m.insert("let", Token::Let);
        m.insert("in", Token::In);
        m.insert("if", Token::If);
        m.insert("then", Token::Then);
        m.insert("else", Token::Else);
        m.insert("match", Token::Match);
        m.insert("with", Token::With);
        m.insert("where", Token::Where);

        m.insert("True", Token::True);
        m.insert("False", Token::False);

        // Built types
        m.insert("u8", Token::U8);
        m.insert("u16", Token::U16);
        m.insert("u32", Token::U32);
        m.insert("u64", Token::U64);
        m.insert("i8", Token::I8);
        m.insert("i16", Token::I16);
        m.insert("i32", Token::I32);
        m.insert("i64", Token::I64);
        m.insert("bool", Token::Bool);

        // Operators
        m.insert("+", Token::Plus);
        m.insert("-", Token::Sub);
        m.insert("*", Token::Mul);
        m.insert("/", Token::Slash);
        m.insert("%", Token::Mod);
        m.insert("**", Token::Pow);
        m.insert("=", Token::Assign);
        m.insert("==", Token::Equal);
        m.insert("!=", Token::NotEqual);
        m.insert("=>", Token::FatArrow);
        m.insert("->", Token::Arrow);
        m.insert("::", Token::Concat);
        m.insert("|", Token::Bar);
        m.insert("or", Token::Or);
        m.insert("and", Token::And);
        m.insert("not", Token::Not);
        m.insert(".", Token::Dot);

        // Separators
        m.insert("(", Token::LParen);
        m.insert(")", Token::RParen);
        m.insert("[", Token::LBrace);
        m.insert("]", Token::RBrace);
        m.insert("{", Token::LCurly);
        m.insert("}", Token::RCurly);
        m.insert("<", Token::LArrow);
        m.insert(">", Token::RArrow);
        m.insert(",", Token::Comma);
        m.insert(":", Token::Colon);
        m.insert("'", Token::Quote);

        m
    };
}

#[derive(Debug)]
pub struct TokenStream(pub VecDeque<Token>, bool, bool);

impl TokenStream {
    fn consume_nl(&mut self) {
        while self.0.front() == Some(&Token::NL) {
            self.2 = true;
            self.0.pop_front();
        }
    }

    pub fn consume(&mut self, t: Token) -> Option<()> {
        if self.test(t.clone()) {
            self.assert(t).unwrap();
            Some(())
        } else {
            None
        }
    }

    pub fn peek(&mut self) -> Option<&Token> {
        if !self.1 {
            self.consume_nl();
        }
        self.0.get(0)
    }

    pub fn next(&mut self) -> Option<Token> {
        if !self.1 {
            self.consume_nl();
        }
        self.0.pop_front()
    }

    pub fn test(&mut self, t: Token) -> bool {
        if !self.1 {
            self.consume_nl();
        }
        if let Some(l) = self.0.get(0) {
            *l == t
        } else {
            false
        }
    }

    pub fn assert(&mut self, t: Token) -> Result<(), String> {
        if !self.1 {
            self.consume_nl();
        }

        if let Some(l) = self.0.pop_front() {
            if l == t {
                Ok(())
            } else {
                Err(format!("Expected '{}', found '{}'", t.name(), l.name()))
            }
        } else {
            Err(format!("Expected '{}', found EOF", t.name()))
        }
    }

    pub fn ident(&mut self) -> Result<String, String> {
        if !self.1 {
            self.consume_nl();
        }

        if let Some(l) = self.0.pop_front() {
            if let Token::Ident(s) = l {
                Ok(s)
            } else {
                self.0.push_front(l.clone());
                Err(format!("Expected identifier, found '{}'", l.name()))
            }
        } else {
            Err(format!("Expected identifier, found EOF"))
        }
    }

    pub fn nl_aware(&mut self) {
        self.1 = true;
        if self.2 {
            self.0.push_front(Token::NL);
            self.2 = false;
        }
    }

    pub fn nl_ignore(&mut self) {
        self.1 = false;
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token {
    // Keywords
    From,
    As,
    Alias,
    Pub,
    Type,
    Let,
    In,
    Typefn,
    Impl,
    For,
    If,
    Then,
    Else,
    Match,
    With,
    Extern,
    Import,
    Where,

    True,
    False,

    // Builtin Types
    Bool,
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,

    // Operators
    Plus,
    Mul,
    Sub,
    Div,
    Slash,
    Mod,
    Pow,
    Assign,
    Equal,
    NotEqual,
    Or,
    And,
    Not,
    LTE,
    GTE,
    Dot,
    Quote,

    // Fancy stuff maybe?
    Arrow,
    FatArrow,
    Concat,
    Bar,

    // Separators
    LArrow,
    RArrow,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LCurly,
    RCurly,
    Comma,
    Colon,

    NL,

    Num(u64),
    Char(char),
    String(String),
    Ident(String),
}

impl Token {
    pub fn name(&self) -> String {
        match self {
            Self::NL => "\\n",
            Self::Quote => "'",
            Self::From => "from",
            Self::As => "as",
            Self::Alias => "alias",
            Self::Pub => "pub",
            Self::True => "True",
            Self::False => "False",
            Self::Bool => "bool",
            Self::Where => "where",
            Self::With => "with",
            Self::Then => "then",
            Self::In => "in",
            Self::Extern => "extern",
            Self::FatArrow => "=>",
            Self::Type => "type",
            Self::Let => "let",
            Self::Typefn => "typefn",
            Self::Impl => "impl",
            Self::For => "for",
            Self::If => "if",
            Self::Else => "else",
            Self::Match => "match",
            Self::Import => "import",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::Plus => "+",
            Self::Mul => "*",
            Self::Sub => "-",
            Self::Slash => "/",
            Self::Div => "//",
            Self::Mod => "%",
            Self::Pow => "**",
            Self::Assign => "=",
            Self::Equal => "==",
            Self::NotEqual => "!=",
            Self::Or => "||",
            Self::And => "&&",
            Self::Not => "!",
            Self::LTE => "<=",
            Self::GTE => ">=",
            Self::Dot => ".",
            Self::Arrow => "->",
            Self::Concat => "::",
            Self::Bar => "|",
            Self::LArrow => "<",
            Self::RArrow => ">",
            Self::LParen => "(",
            Self::RParen => ")",
            Self::LBrace => "[",
            Self::RBrace => "]",
            Self::LCurly => "{",
            Self::RCurly => "}",
            Self::Comma => ",",
            Self::Colon => ":",
            Self::Num(n) => return n.to_string(),
            Self::Char(c) => return c.to_string(),
            Self::String(s) => s,
            Self::Ident(s) => s,
        }
        .into()
    }
}

#[derive(Default)]
pub struct Lexer {
    in_string: bool,
    in_comment: bool,
}

impl Lexer {
    pub fn lex(&mut self, input: &str) -> Result<TokenStream, String> {
        let mut tokens = VecDeque::new();
        let mut chars = input.chars().peekable();

        let mut stack = String::new();

        while let Some(c) = chars.next() {
            let next = chars.peek();

            // If we are in a single line comment go to end of line
            if self.in_comment {
                if c == '\n' {
                    self.in_comment = false;
                    tokens.push_back(Token::NL);
                }
                continue;
            }

            // If we are in a string skip all characters until "
            // while also transforming escape sequences
            if self.in_string {
                match c {
                    '"' => {
                        self.push_token(&mut tokens, &mut stack);
                        self.in_string = false;
                    }
                    '\\' => {
                        let new_c = match next {
                            Some('a') => char::from_u32(7).unwrap(),
                            Some('b') => char::from_u32(8).unwrap(),
                            Some('f') => char::from_u32(12).unwrap(),
                            Some('n') => '\n',
                            Some('r') => '\r',
                            Some('t') => '\t',
                            Some('v') => char::from_u32(11).unwrap(),
                            Some('\\') => '\\',
                            Some('"') => '"',
                            Some('?') => '?',
                            Some('0') => char::from_u32(0).unwrap(),
                            _ => return Err("Invalid escape sequence".to_string()),
                        };

                        stack.push(new_c);
                        chars.next();
                    }
                    _ => stack.push(c),
                }
                continue;
            }

            match c {
                // Enter a comment
                '#' => {
                    self.push_token(&mut tokens, &mut stack);
                    self.in_comment = true;
                }
                // Enter a string literal
                '"' => {
                    self.push_token(&mut tokens, &mut stack);
                    self.in_string = true;
                }
                // Char Literal or type var...
                '\'' if stack.is_empty() => {
                    self.push_token(&mut tokens, &mut stack);

                    let val = chars.next().ok_or("Expected char literal".to_string())?;

                    let (c, n) = if val == '\\' {
                        let escape = chars
                            .next()
                            .ok_or("Expected escape character".to_string())?;
                        let new_c = match escape {
                            'a' => char::from_u32(7).unwrap(),
                            'b' => char::from_u32(8).unwrap(),
                            'f' => char::from_u32(12).unwrap(),
                            'r' => '\r',
                            't' => '\t',
                            'n' => '\n',
                            '\'' => '\'',
                            'v' => char::from_u32(11).unwrap(),
                            '\\' => '\\',
                            '"' => '"',
                            '?' => '?',
                            '0' => char::from_u32(0).unwrap(),
                            _ => return Err("Invalid escape sequence".to_string()),
                        };
                        (new_c, 3)
                    } else {
                        (val, 2)
                    };

                    if let Some('\'') = chars.peek() {
                        chars.next();
                        tokens.push_back(Token::Char(c));
                    } else if n == 3 {
                        return Err("ahhh".to_string());
                    } else {
                        // not a char literal, parse as type var
                        tokens.push_back(Token::Quote);
                        stack.push(c);
                    }
                }
                // Some fancy double char operators???
                '*' if next.is_some() && *next.unwrap() == '*' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push_back(Token::Pow);
                }
                ':' if next.is_some() && *next.unwrap() == ':' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push_back(Token::Concat);
                }
                '-' if next.is_some() && *next.unwrap() == '>' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push_back(Token::Arrow);
                }
                '|' if next.is_some() && *next.unwrap() == '|' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push_back(Token::Or);
                }
                '&' if next.is_some() && *next.unwrap() == '&' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push_back(Token::And);
                }
                '=' if next.is_some() && *next.unwrap() == '=' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push_back(Token::Equal);
                }
                '!' if next.is_some() && *next.unwrap() == '=' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push_back(Token::NotEqual);
                }
                '<' if next.is_some() && *next.unwrap() == '=' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push_back(Token::LTE);
                }
                '>' if next.is_some() && *next.unwrap() == '=' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push_back(Token::GTE);
                }
                '=' if next.is_some() && *next.unwrap() == '>' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push_back(Token::FatArrow)
                }
                '/' if next.is_some() && *next.unwrap() == '/' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push_back(Token::Div)
                }
                // Separators
                ',' | '(' | ')' | '[' | ']' | '{' | '}' | ':' => {
                    self.push_token(&mut tokens, &mut stack);
                    tokens.push_back(MAP.get(c.to_string().as_str()).unwrap().clone());
                }

                // Single char Operators
                '+' | '-' | '*' | '/' | '%' | '<' | '>' | '=' => {
                    self.push_token(&mut tokens, &mut stack);
                    tokens.push_back(MAP.get(c.to_string().as_str()).unwrap().clone());
                }
                '!' if stack.is_empty() => {
                    self.push_token(&mut tokens, &mut stack);
                    tokens.push_back(MAP.get(c.to_string().as_str()).unwrap().clone());
                }
                '\n' => {
                    self.push_token(&mut tokens, &mut stack);
                    tokens.push_back(Token::NL);
                }
                ' ' | '\t' => {
                    self.push_token(&mut tokens, &mut stack);
                }
                _ => {
                    stack.push(c);
                }
            }
        }

        if self.in_string {
            return Err(format!("Unclosed string literal: expected \""));
        }

        self.push_token(&mut tokens, &mut stack);

        Ok(TokenStream(tokens, false, false))
    }

    fn push_token(&mut self, tokens: &mut VecDeque<Token>, stack: &mut String) {
        if !stack.is_empty() {
            if self.in_string {
                tokens.push_back(Token::String(stack.clone()));
            } else if let Some(tok) = MAP.get(stack.as_str()) {
                tokens.push_back(tok.clone());
            } else if let Ok(i) = str::parse::<u64>(&stack) {
                tokens.push_back(Token::Num(i));
            } else {
                tokens.push_back(Token::Ident(stack.clone()));
            }

            stack.clear();
        }
    }
}
