use crate::parse_tree::Type;
use crate::parse_tree::TypeCons;

use std::collections::HashMap;

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum LLVMType {
    I1,
    I8,
    U8,
    I16,
    U16,
    I32,
    U32,
    I64,
    U64,
    Ptr(Box<LLVMType>),
    Str,
    Void,
    Func(Box<LLVMType>, Box<LLVMType>),
    Struct(Vec<LLVMType>),
    Array(Box<LLVMType>, usize),
    Named(String),
}

impl LLVMType {
    pub fn from_type(t: Type) -> Self {
        match t {
            Type::I8 => Self::I8,
            Type::U8 => Self::U8,
            Type::I16 => Self::I16,
            Type::U16 => Self::U16,
            Type::I32 => Self::I32,
            Type::U32 => Self::U32,
            Type::I64 => Self::I64,
            Type::U64 => Self::U64,
            Type::Str => Self::Str,
            Type::Unit => Self::Void,
            Type::Arrow(a, b) => Self::Func(
                Box::new(LLVMType::from_type(*a)),
                Box::new(LLVMType::from_type(*b)),
            ),
            //Type::Tuple(_) => Self::Ptr,
            Type::Tuple(ts) => {
                Self::Struct(ts.into_iter().map(|t| LLVMType::from_type(t)).collect())
            }
            Type::Ident(n) => Self::Named(n),
            Type::Generic(..) => Self::Named(t.to_string()),
            Type::Box(n) => Self::Ptr(Box::new(LLVMType::from_type(*n))),
            _ => panic!(),
        }
    }

    pub fn from_enum(cons: Vec<TypeCons>) -> Vec<(String, LLVMType)> {
        let mut types = vec![];
        for TypeCons { name, args, .. } in cons {
            match Self::from_type(args) {
                Self::Struct(mut ts) => {
                    ts.insert(0, LLVMType::I8);
                    types.push((name, Self::Struct(ts)))
                }
                Self::Void => types.push((name, Self::Struct(vec![LLVMType::I8]))),
                ty => types.push((name, Self::Struct(vec![LLVMType::I8, ty]))),
            }
        }

        types
    }

    pub fn from_struct(mems: Vec<(String, Type)>) -> Self {
        let mut inner = vec![];

        for (_, t) in mems {
            inner.push(Self::from_type(t));
        }

        Self::Struct(inner)
    }

    pub fn from_cons(t: TypeCons) -> Self {
        Self::from_type(t.args)
    }

    pub fn size(&self, mut curr: usize, types: &HashMap<String, usize>) -> Option<usize> {
        let my_align = self.alignment();
        curr += curr % my_align;

        match self {
            Self::Void => {}
            Self::I1 => curr += 1,
            Self::I8 => curr += 8,
            Self::U8 => curr += 8,
            Self::I16 => curr += 16,
            Self::U16 => curr += 16,
            Self::I32 => curr += 32,
            Self::U32 => curr += 32,
            Self::I64 => curr += 64,
            Self::U64 => curr += 64,
            Self::Ptr(_) => curr += 64,
            Self::Str => curr += 64,
            Self::Struct(ts) => {
                for t in ts {
                    let t_align = t.alignment();
                    curr += curr % t_align;
                    curr = t.size(curr, types)?;
                }
            }
            Self::Array(t, num) => {
                curr += t.size(0, types)? * num;
            }
            Self::Func(..) => curr += 64,
            Self::Named(name) => {
                curr += types.get(name)?;
            }
        };

        Some(curr)
    }

    pub fn alignment(&self) -> usize {
        match self {
            Self::Void => 0,
            Self::I1 => 8,
            Self::I8 => 8,
            Self::U8 => 8,
            Self::I16 => 16,
            Self::U16 => 16,
            Self::I32 => 32,
            Self::U32 => 32,
            Self::I64 => 64,
            Self::U64 => 64,
            Self::Ptr(_) => 64,
            Self::Str => 64,
            Self::Struct(..) => 64,
            Self::Array(..) => 64,
            Self::Func(..) => 64,
            Self::Named(..) => 64,
        }
    }
}

impl std::fmt::Display for LLVMType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::I1 => f.write_str("i1"),
            Self::I8 => f.write_str("i8"),
            Self::U8 => f.write_str("i8"),
            Self::I16 => f.write_str("i16"),
            Self::U16 => f.write_str("i16"),
            Self::I32 => f.write_str("i32"),
            Self::U32 => f.write_str("i32"),
            Self::I64 => f.write_str("i64"),
            Self::U64 => f.write_str("i64"),
            Self::Ptr(_) => f.write_str("ptr"),
            Self::Str => f.write_str("ptr"),
            Self::Void => f.write_str("void"),
            Self::Struct(ts) => {
                f.write_str("{")?;

                let mut ts = ts.into_iter();
                f.write_fmt(format_args!("{}", ts.next().unwrap()))?;

                for t in ts {
                    f.write_str(", ")?;
                    f.write_fmt(format_args!("{t}"))?;
                }

                f.write_str("}")
            }
            Self::Array(t, num) => f.write_fmt(format_args!("[{num} x {t}]")),
            Self::Named(n) => f.write_fmt(format_args!("%{n}")),
            Self::Func(..) => f.write_str("ptr"),
        }
    }
}
