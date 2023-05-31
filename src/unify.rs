use std::collections::HashMap;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Term<T: std::cmp::Eq + std::hash::Hash + Clone> {
    Var(usize),
    Const(T),
    Composite(T, Vec<Term<T>>)
}

impl Term<String> {
    pub fn name(&self) -> String {
        match self {
            Self::Var(_) => "?".to_string(),
            Self::Const(s) => s.clone(),
            Self::Composite(s, ts) => {
                match s.as_str() {
                    "->" => format!("{} -> {}", ts[0].name(), ts[1].name()),
                    "list" => format!("[{}]", ts[0].name()),
                    "tuple" => format!("({})", ts.iter().map(|t| t.name()).collect::<Vec<_>>().join(", ")),
                    a => format!("{a}<{}>", ts.iter().map(|t| t.name()).collect::<Vec<_>>().join(", "))
                }
            }
        }
    }
}


fn occurs_check<'a, T>(
    x: &'a Term<T>,
    t: &'a Term<T>,
    subs: &mut HashMap<Term<T>, Term<T>>,
) -> bool
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
    T: std::cmp::Eq + std::hash::Hash + Clone
{
    while subs.contains_key(&s) {
        s = subs.get(&s).unwrap().clone();
    }

    match s {
        Term::Composite(t, ts) => Term::Composite(t, ts.into_iter().map(|t| apply_unifier(t, subs)).collect()),
        a => a
    }
}


pub fn unify<T>(s: Term<T>, t: Term<T>, mut subs: HashMap<Term<T>, Term<T>>) -> Option<HashMap<Term<T>, Term<T>>>
where
    T: std::cmp::Eq + std::hash::Hash + Clone + std::fmt::Debug,
{
    let mut stack: Vec<(Term<T>, Term<T>)> = vec![(s, t)];

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
                (&Term::Var(_), _) => if occurs_check(&s, &t, &mut subs) {
                    subs.insert(s.clone(), t.clone());
                } else {
                    return None;
                },
                (_, &Term::Var(_)) => if occurs_check(&t, &s, &mut subs) {
                    subs.insert(t.clone(), s.clone());
                } else {
                    return None;
                },
                (
                    &Term::Composite(ref s_name, ref s_terms),
                    &Term::Composite(ref t_name, ref t_terms),
                ) => if s_name == t_name && s_terms.len() == t_terms.len() {
                    for (s, t) in s_terms.iter().zip(t_terms) {
                        stack.push((s.clone(), t.clone()));
                    }
                } else {
                    return None;
                },
                (_, _) => return None,
            }
        }
    }

    Some(subs)
}
