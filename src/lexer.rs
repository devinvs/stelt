use std::collections::HashMap;

use lazy_static::lazy_static;

lazy_static! {
    pub static ref MAP: HashMap<&'static str, Token> = {
        let mut m = HashMap::new();

        // Keywords
        m.insert("def", Token::Def);
        m.insert("let", Token::Let);
        m.insert("type", Token::Type);

        // Built types
        m.insert("u8", Token::U8);
        m.insert("u16", Token::U16);
        m.insert("u32", Token::U32);
        m.insert("u64", Token::U64);
        m.insert("i8", Token::I8);
        m.insert("i16", Token::I16);
        m.insert("i32", Token::I32);
        m.insert("i64", Token::I64);

        // Operators
        m.insert("+", Token::Plus);
        m.insert("-", Token::Sub);
        m.insert("*", Token::Times);
        m.insert("/", Token::Div);
        m.insert("%", Token::Mod);
        m.insert("**", Token::Pow);
        m.insert("=", Token::Equal);
        m.insert("->", Token::Arrow);
        m.insert("_", Token::Underscore);
        m.insert("::", Token::Concat);
        m.insert("|", Token::Bar);

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

        m
    };
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token {
    Def,
    Type,
    Let,

    // Builtin Types
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
    Times,
    Sub,
    Div,
    Mod,
    Pow,
    Equal,

    // Fancy stuff maybe?
    Arrow,
    Underscore,
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

    Num(u64),
    Char(char),
    String(String),
    Ident(String),
}

impl Token {
    pub fn isdef(&self) -> bool { self==&Token::Def }
    pub fn istype(&self) -> bool { self==&Token::Type }
    pub fn islet(&self) -> bool { self==&Token::Let }

    pub fn isu8(&self) -> bool { self==&Token::U8 }
    pub fn isu16(&self) -> bool { self==&Token::U16 }
    pub fn isu32(&self) -> bool { self==&Token::U32 }
    pub fn isu64(&self) -> bool { self==&Token::U64 }
    pub fn isi8(&self) -> bool { self==&Token::I8 }
    pub fn isi16(&self) -> bool { self==&Token::I16 }
    pub fn isi32(&self) -> bool { self==&Token::I32 }
    pub fn isi64(&self) -> bool { self==&Token::I64 }

    pub fn isnum(&self) -> bool { if let Token::Num(_) = self { true } else { false } }
    pub fn isident(&self) -> bool { if let Token::Ident(_) = self { true } else { false } }
}

#[derive(Default)]
pub struct Lexer {
    in_string: bool,
    in_comment: bool
}

impl Lexer {
    pub fn lex(&mut self, input: &str) -> Vec<Token> {
        let mut tokens = Vec::new();
        let mut chars = input.chars().peekable();

        let mut stack = String::new();

        while let Some(c) = chars.next() {
            let next = chars.peek();

            // If we are in a single line comment go to end of line
            if self.in_comment {
                if c == '\n' {
                    self.in_comment = false;
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
                                _ => panic!("Invalid escape sequence")
                            };

                            stack.push(new_c);
                            chars.next();
                    }
                    _ => stack.push(c)
                }
                continue;
            }

            match c {
                // Enter a comment
                '/' if next.is_some() && *next.unwrap()=='/' => {
                    self.push_token(&mut tokens, &mut stack);
                    self.in_comment = true;
                }
                // Enter a string literal
                '"' => {
                    self.push_token(&mut tokens, &mut stack);
                }
                // Char Literal
                '\'' if stack.is_empty() => {
                    self.push_token(&mut tokens, &mut stack);

                    let val = chars.next().unwrap();
                    if val == '\\' {
                        let escape = chars.next().unwrap();
                        let new_c = match escape {
                                'a' => char::from_u32(7).unwrap(),
                                'b' => char::from_u32(8).unwrap(),
                                'f' => char::from_u32(12).unwrap(),
                                'r' => '\r',
                                't' => '\t',
                                'v' => char::from_u32(11).unwrap(),
                                '\\' => '\\',
                                '"' => '"',
                                '?' => '?',
                                '0' => char::from_u32(0).unwrap(),
                                _ => panic!("Invalid escape sequence")
                            };
                        tokens.push(Token::Char(new_c));
                    } else {
                        tokens.push(Token::Char(val));
                    }
                    println!("{val}");

                    assert_eq!(chars.next().unwrap(), '\'');
                }
                // Some fancy double char operators???
                '*' if next.is_some() && *next.unwrap() == '*' => {
                    chars.next().unwrap();
                    tokens.push(Token::Pow);
                }
                ':' if next.is_some() && *next.unwrap() == ':' => {
                    chars.next().unwrap();
                    tokens.push(Token::Concat);
                }
                '-' if next.is_some() && *next.unwrap() == '>' => {
                    chars.next().unwrap();
                    tokens.push(Token::Arrow);
                }
                // Separators
                ',' | '(' | ')' | '[' | ']' | '{' | '}' => {
                    self.push_token(&mut tokens, &mut stack);
                    tokens.push(MAP.get(c.to_string().as_str()).unwrap().clone());
                }

                // Single char Operators
                '+' | '-' | '*' | '/' | '%' | '<' | '>' | '=' | '|' => {
                    self.push_token(&mut tokens, &mut stack);
                    tokens.push(MAP.get(c.to_string().as_str()).unwrap().clone());
                }
                ' ' | '\n' | '\t' => self.push_token(&mut tokens, &mut stack),
                _ => {
                    stack.push(c);
                }
            }
        }

        tokens
    }

    fn push_token(&mut self, tokens: &mut Vec<Token>, stack: &mut String) {
        if !stack.is_empty() {
            if self.in_string {
                tokens.push(Token::String(stack.clone()));
            } else if let Some(tok) = MAP.get(stack.as_str()) {
                tokens.push(tok.clone());
            } else if let Ok(i) = str::parse::<u64>(&stack) {
                tokens.push(Token::Num(i));
            } else {
                tokens.push(Token::Ident(stack.clone()));
            }

            stack.clear();
        }
    }
}
