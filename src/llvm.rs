use crate::parse_tree::Type;
use crate::parse_tree::TypeCons;

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum LLVMType {
    I1,
    I8,
    I32,
    Ptr,
    Void,
    Func(Box<LLVMType>, Box<LLVMType>),
    Struct(Vec<LLVMType>),
    Array(Box<LLVMType>, usize),
    Named(String),
}

impl LLVMType {
    pub fn from_type(t: Type) -> Self {
        match t {
            Type::I32 => Self::I32,
            Type::I8 => Self::I8,
            Type::Str => Self::Ptr,
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
            a => unimplemented!("{a:?}"),
        }
    }

    pub fn from_enum(tname: &String, cons: Vec<TypeCons>) -> Vec<(String, LLVMType)> {
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

    pub fn size(&self, mut curr: usize) -> usize {
        let my_align = self.alignment();
        curr += curr % my_align;

        match self {
            Self::Void => {}
            Self::I8 => curr += 8,
            Self::I1 => curr += 1,
            Self::I32 => curr += 32,
            Self::Ptr => curr += 64,
            Self::Struct(ts) => {
                for t in ts {
                    let t_align = t.alignment();
                    curr += curr % t_align;
                    curr = t.size(curr)
                }
            }
            Self::Array(t, num) => {
                curr += t.size(0) * num;
            }
            Self::Func(..) => curr += 64,
            Self::Named(_) => panic!("size unknown for named type"),
        };

        curr
    }

    pub fn alignment(&self) -> usize {
        match self {
            Self::Void => 0,
            Self::I1 => 8,
            Self::I8 => 8,
            Self::I32 => 32,
            Self::Ptr => 64,
            Self::Struct(..) => 64,
            Self::Array(..) => 64,
            Self::Func(..) => 64,
            Self::Named(n) => panic!("alignment unknown for named type: {n}"),
        }
    }
}

impl std::fmt::Display for LLVMType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::I1 => f.write_str("i1"),
            Self::I8 => f.write_str("i8"),
            Self::I32 => f.write_str("i32"),
            Self::Ptr => f.write_str("ptr"),
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
