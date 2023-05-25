use crate::parse_tree::Type;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum LLVMType {
    I1,
    I8,
    I32,
    Ptr,
    Void,
    Struct(Vec<LLVMType>)
}

impl LLVMType {
    pub fn from_type(t: Type) -> Self {
        match t {
            Type::I32 => Self::I32,
            Type::I8 => Self::I8,
            Type::Str => Self::Ptr,
            Type::Unit => Self::Void,
            Type::Arrow(_, _) => Self::Ptr,
            Type::Tuple(ts) => Self::Struct(ts.into_iter().map(|t| LLVMType::from_type(t)).collect()),
            a => unimplemented!("{a:?}")
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
        }
    }
}
