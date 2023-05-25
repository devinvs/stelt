use crate::parse_tree::Type;

#[derive(Debug, PartialEq, Eq)]
pub enum LLVMType {
    I8,
    I32,
    Ptr,
    Void,
}

impl LLVMType {
    pub fn from_type(t: Type) -> Self {
        match t {
            Type::I32(_) => Self::I32,
            Type::I8(_) => Self::I8,
            Type::Str(_) => Self::Ptr,
            Type::Unit(_) => Self::Void,
            a => unimplemented!("{a:?}")
        }
    }
}

impl std::fmt::Display for LLVMType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::I8 => f.write_str("i8"),
            Self::I32 => f.write_str("i32"),
            Self::Ptr => f.write_str("ptr"),
            Self::Void => f.write_str("void")
        }
    }
}
