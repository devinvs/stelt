/*use std::collections::HashMap;

use crate::ast::{Program, Type, Field, Function, Expression};

// Simple Representation of a type in memory
enum TypeLayout {
    // Regular LLVM Types
    I1,
    I8,
    I16,
    I32,
    I64,
    Void,

    Pointer,

    // containers
    Vec(Vec<TypeLayout>),
}

impl TypeLayout {
    fn join(mut self, mut other: TypeLayout) -> TypeLayout {
        let v = if let Self::Vec(a) = self {
            a.push(other);
            a
        } else if let Self::Vec(b) = other {
            b.push(self);
            b
        } else {
            vec![self, other]
        };

        TypeLayout::Vec(v)
    }
}

// We should be able to convert any type that we have into a type representation for llvm
impl Type {
    fn layout(&self, types: HashMap<>) -> TypeLayout {
        match self {
            Self::Simple(_) => TypeLayout::Void,
            Self::Struct(_, fs) => {
                TypeLayout::Vec(
                fs.iter().fold(TypeLayout::Vec(vec![]), |a, f| {
                    a.join(f.layout(types))
                })
            }
            Self::Union(_, ts) => {
                let mut tls = vec![];
                tls.push(TypeLayout::I8);

                for t in ts {
                    tls.push(t.layout());
                }
                TypeLayout::Vec(tls)
            }
        }
    }
}

impl Field {
    fn layout(&self, types: HashMap<String, TypeLayout>) -> TypeLayout {
        match self {
            Self::Bool => TypeLayout::I1,
            Self::U8 | Self::I8 => TypeLayout::I8,
            Self::U16 | Self::I16 => TypeLayout::I16,
            Self::U32 | Self::I32 => TypeLayout::I32,
            Self::U64 | Self::I64 => TypeLayout::I64,
            Self::Empty => TypeLayout::Void,
            Self::Func(_, _) => TypeLayout::Pointer,
            Self::Tuple(fs) => TypeLayout::Vec(fs.iter().map(|f| f.layout()).collect()),
            Self::Ident(t) => {
                *types.get(t).unwrap()
            }
        }
    }
}

impl Program {
    fn infer_types(&mut self) {
        for (_, fs) in self.funcs.iter_mut() {
            for f in fs.iter_mut() {
                f.infer_types(&self.types);
            }
        }
    }
}

impl Function {
    fn infer_types(&mut self, types: &HashMap<String, Type>) {

    }
}

impl Expression {
    fn infer_types(&mut self, types: &HashMap<String, Type>) {
        match self {
            Self::Let(f, name, e) => {
                e.infer_types(types);
                *f = e.ty();
            }
            Self::Concat(f, l, r) => {
                l.infer_types(types);
                r.infer_types(types);

                if let Some(Field::List(a)) = l.ty() {
                    if r.ty() != Some(*a) {
                        panic!("Invalid Concat")
                    }

                    *f = Some(Field::List(a))
                } else if let Some(Field::List(a)) = r.ty() {
                    if l.ty() != Some(*a) {
                        panic!("Invalid Concat")
                    }

                    *f = Some(Field::List(a))
                } else if l.ty() == r.ty() {
                    *f = Some(Field::List(Box::new(l.ty().unwrap())))
                } else {
                    panic!("Invalid Concat")
                }
            }
            Self::Or(f, l, r) => {
                l.infer_types(types);
                r.infer_types(types);

                if l.ty() == Some(Field::Bool) && r.ty() == Some(Field::Bool) {
                    *f = Some(Field::Bool);
                } else {
                    panic!("Invalid Or")
                }
            }
            Self::And(f, l, r) => {
                l.infer_types(types);
                r.infer_types(types);

                if l.ty() == Some(Field::Bool) && r.ty() == Some(Field::Bool) {
                    *f = Some(Field::Bool);
                } else {
                    panic!("Invalid And")
                }
            }
            Self::BitOr(f, l, r) => {
                l.infer_types(types);
                r.infer_types(types);

                if l.ty() == Some(Field::Bool) && r.ty() == Some(Field::Bool) {
                    *f = Some(Field::Bool);
                } else {
                    panic!("Invalid And")
                }
            }
        }
    }
}*/
