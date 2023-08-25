use std::collections::HashMap;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Term<T: std::cmp::Eq + std::hash::Hash + Clone> {
    Var(usize),
    Number(usize),
    Const(T),
    Composite(T, Vec<Term<T>>),
}

impl Term<String> {
    pub fn name(&self) -> String {
        match self {
            Self::Var(_) => "?".to_string(),
            Self::Const(s) => s.clone(),
            Self::Composite(s, ts) => match s.as_str() {
                "->" => format!("{} -> {}", ts[0].name(), ts[1].name()),
                "list" => format!("[{}]", ts[0].name()),
                "tuple" => format!(
                    "({})",
                    ts.iter().map(|t| t.name()).collect::<Vec<_>>().join(", ")
                ),
                a => format!(
                    "{a}<{}>",
                    ts.iter().map(|t| t.name()).collect::<Vec<_>>().join(", ")
                ),
            },
            Self::Number(_) => "i?".to_string(),
        }
    }
}

fn occurs_check<'a, T>(x: &'a Term<T>, t: &'a Term<T>, subs: &mut HashMap<Term<T>, Term<T>>) -> bool
where
    T: std::cmp::Eq + std::hash::Hash + Clone,
{
    let mut stack: Vec<&Term<T>> = vec![t];

    fn get_vars<'a, T: std::cmp::Eq + std::hash::Hash + Clone>(t: &'a Term<T>) -> Vec<&'a Term<T>> {
        match t {
            &Term::Var(_) => vec![t],
            &Term::Composite(_, ref terms) => {
                let mut v = vec![];
                for term in terms {
                    v.append(&mut get_vars(&term));
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
            } else if subs.contains_key(y) {
                stack.push(&subs[y]);
            }
        }
    }

    true
}

pub fn apply_unifier<T>(mut s: Term<T>, subs: &HashMap<Term<T>, Term<T>>) -> Term<T>
where
    T: std::cmp::Eq + std::hash::Hash + Clone + std::fmt::Debug,
{
    while subs.contains_key(&s) {
        s = subs.get(&s).unwrap().clone();
    }

    match s {
        Term::Composite(t, ts) => {
            Term::Composite(t, ts.into_iter().map(|t| apply_unifier(t, subs)).collect())
        }
        a => a,
    }
}

pub fn unify(
    s: Term<String>,
    t: Term<String>,
    mut subs: HashMap<Term<String>, Term<String>>,
) -> Option<HashMap<Term<String>, Term<String>>> {
    let mut stack: Vec<(Term<String>, Term<String>)> = vec![(s, t)];

    while !stack.is_empty() {
        let (mut s, mut t) = stack.pop().unwrap();

        while subs.contains_key(&s) {
            s = subs.get(&s).unwrap().clone()
        }

        while subs.contains_key(&t) {
            t = subs.get(&t).unwrap().clone()
        }

        if s != t {
            match (&s, &t) {
                (&Term::Var(_), &Term::Var(_)) => {
                    subs.insert(s.clone(), t.clone());
                }
                (&Term::Number(_), &Term::Number(_)) => {
                    subs.insert(s.clone(), t.clone());
                }
                (&Term::Var(_), &Term::Number(_)) => {
                    subs.insert(s.clone(), t.clone());
                }
                (&Term::Number(_), &Term::Var(_)) => {
                    subs.insert(t.clone(), s.clone());
                }
                (&Term::Var(_), _) => {
                    if occurs_check(&s, &t, &mut subs) {
                        subs.insert(s.clone(), t.clone());
                    } else {
                        return None;
                    }
                }
                (_, &Term::Var(_)) => {
                    if occurs_check(&t, &s, &mut subs) {
                        subs.insert(t.clone(), s.clone());
                    } else {
                        return None;
                    }
                }
                (&Term::Number(_), a)
                    if a == &Term::Const("u8".to_string())
                        || a == &Term::Const("u16".to_string())
                        || a == &Term::Const("u32".to_string())
                        || a == &Term::Const("u64".to_string())
                        || a == &Term::Const("i8".to_string())
                        || a == &Term::Const("i16".to_string())
                        || a == &Term::Const("i32".to_string())
                        || a == &Term::Const("i64".to_string()) =>
                {
                    subs.insert(s.clone(), a.clone());
                }
                (a, &Term::Number(_))
                    if a == &Term::Const("u8".to_string())
                        || a == &Term::Const("u16".to_string())
                        || a == &Term::Const("u32".to_string())
                        || a == &Term::Const("u64".to_string())
                        || a == &Term::Const("i8".to_string())
                        || a == &Term::Const("i16".to_string())
                        || a == &Term::Const("i32".to_string())
                        || a == &Term::Const("i64".to_string()) =>
                {
                    subs.insert(t.clone(), a.clone());
                }
                (
                    &Term::Composite(ref s_name, ref s_terms),
                    &Term::Composite(ref t_name, ref t_terms),
                ) => {
                    if s_name == t_name && s_terms.len() == t_terms.len() {
                        for (s, t) in s_terms.iter().zip(t_terms) {
                            stack.push((s.clone(), t.clone()));
                        }
                    } else {
                        return None;
                    }
                }
                (_, _) => return None,
            }
        }
    }

    Some(subs)
}
