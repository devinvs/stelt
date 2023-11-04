use crate::parse_tree::Type;
use std::collections::HashMap;

fn occurs_check(x: Type, t: Type, subs: &mut HashMap<Type, Type>) -> bool {
    let mut stack: Vec<Type> = vec![t];

    fn get_vars(t: Type) -> Vec<Type> {
        match t {
            Type::Var(_) | Type::NumVar(_) => vec![t],
            Type::Generic(ass, b) => {
                let mut v = vec![];
                for a in ass {
                    v.append(&mut get_vars(a));
                }
                v.append(&mut get_vars(*b));
                v
            }
            Type::Arrow(a, b) => {
                let mut v = vec![];
                v.append(&mut get_vars(*a));
                v.append(&mut get_vars(*b));
                v
            }
            Type::Tuple(ass) => {
                let mut v = vec![];
                for a in ass {
                    v.append(&mut get_vars(a));
                }
                v
            }
            _ => vec![],
        }
    }

    while !stack.is_empty() {
        let t = stack.pop();
        for y in get_vars(t.unwrap()) {
            if x == y {
                return false;
            } else if subs.contains_key(&y) {
                stack.push(subs[&y].clone());
            }
        }
    }

    true
}

pub fn apply_unifier(mut s: Type, subs: &HashMap<Type, Type>) -> Type {
    while subs.contains_key(&s) {
        s = subs.get(&s).unwrap().clone();
    }

    match s {
        Type::Generic(ass, b) => Type::Generic(
            ass.into_iter().map(|t| apply_unifier(t, subs)).collect(),
            Box::new(apply_unifier(*b, subs)),
        ),
        Type::Arrow(a, b) => Type::Arrow(
            Box::new(apply_unifier(*a, subs)),
            Box::new(apply_unifier(*b, subs)),
        ),
        Type::Tuple(ass) => Type::Tuple(ass.into_iter().map(|t| apply_unifier(t, subs)).collect()),
        a => a,
    }
}

pub fn unify(s: Type, t: Type, mut subs: HashMap<Type, Type>) -> Option<HashMap<Type, Type>> {
    let mut stack: Vec<(Type, Type)> = vec![(s, t)];

    while !stack.is_empty() {
        let (mut s, mut t) = stack.pop().unwrap();

        while subs.contains_key(&s) {
            s = subs.get(&s).unwrap().clone();
        }

        while subs.contains_key(&t) {
            t = subs.get(&t).unwrap().clone();
        }

        if s != t {
            match (s.clone(), t.clone()) {
                (Type::Var(_), Type::Var(_)) => {
                    subs.insert(s, t);
                }
                (Type::Var(_), Type::NumVar(_)) => {
                    subs.insert(s, t);
                }
                (Type::NumVar(_), Type::Var(_)) => {
                    subs.insert(t, s);
                }
                (Type::NumVar(_), Type::NumVar(_)) => {
                    subs.insert(s, t);
                }
                (Type::Var(_), _) => {
                    if occurs_check(s.clone(), t.clone(), &mut subs) {
                        subs.insert(s, t);
                    } else {
                        return None;
                    }
                }
                (_, Type::Var(_)) => {
                    if occurs_check(s.clone(), t.clone(), &mut subs) {
                        subs.insert(t, s);
                    } else {
                        return None;
                    }
                }
                (Type::NumVar(_), a)
                    if a == Type::U8
                        || a == Type::U16
                        || a == Type::U32
                        || a == Type::U64
                        || a == Type::I8
                        || a == Type::I16
                        || a == Type::I32
                        || a == Type::I64 =>
                {
                    subs.insert(s, a);
                }
                (a, Type::NumVar(_))
                    if a == Type::U8
                        || a == Type::U16
                        || a == Type::U32
                        || a == Type::U64
                        || a == Type::I8
                        || a == Type::I16
                        || a == Type::I32
                        || a == Type::I64 =>
                {
                    subs.insert(t, a);
                }
                (Type::Generic(ass, b), Type::Generic(cs, d)) => {
                    for (a, c) in ass.into_iter().zip(cs) {
                        stack.push((a, c));
                    }

                    stack.push((*b, *d));
                }
                (Type::Arrow(a, b), Type::Arrow(c, d)) => {
                    stack.push((*a, *c));
                    stack.push((*b, *d));
                }
                (Type::Tuple(ass), Type::Tuple(bs)) => {
                    for (a, b) in ass.into_iter().zip(bs) {
                        stack.push((a, b));
                    }
                }
                (_, _) => return None,
            }
        }
    }

    Some(subs)
}
