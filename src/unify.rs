use crate::parse_tree::Type;
use std::collections::HashMap;

pub type Theta<T> = Option<HashMap<Term<T>, Term<T>>>;

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Term<T: std::cmp::Eq + std::hash::Hash> {
    Var(usize),
    Const(T),
    Composite(T, Vec<Term<T>>)
}

fn occurs_check<'a, T>(
    x: &'a Term<T>,
    t: &'a Term<T>,
    subs: &mut HashMap<&'a Term<T>, &'a Term<T>>,
) -> bool
where
    T: std::cmp::Eq + std::hash::Hash,
{
    let mut stack: Vec<&Term<T>> = vec![t];

    fn get_vars<'a, T: std::cmp::Eq + std::hash::Hash>(t: &'a Term<T>) -> Vec<&'a Term<T>> {
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
                stack.push(subs[y]);
            }
        }
    }

    true
}

pub fn unify<'a, T>(s: &'a Term<T>, t: &'a Term<T>, mut subs: HashMap<&Term<T>, &Term<T>>) -> Option<HashMap<&'a Term<T>, &'a Term<T>>>
where
    T: std::cmp::Eq + std::hash::Hash,
{
    let mut stack: Vec<(&Term<T>, &Term<T>)> = vec![(s, t)];

    while !stack.is_empty() {
        let (mut s, mut t) = stack.pop().unwrap();

        while subs.contains_key(&s) {
            s = subs.get(&s).unwrap()
        }

        while subs.contains_key(&t) {
            t = subs.get(&t).unwrap()
        }

        if s != t {
            match (s, t) {
                (&Term::Var(_), &Term::Var(_)) => {
                    subs.insert(s, t);
                }
                (&Term::Var(_), _) => if occurs_check(s, t, &mut subs) {
                    subs.insert(s, t);
                } else {
                    return None;
                },
                (_, &Term::Var(_)) => if occurs_check(t, s, &mut subs) {
                    subs.insert(t, s);
                } else {
                    return None;
                },
                (
                    &Term::Composite(ref s_name, ref s_terms),
                    &Term::Composite(ref t_name, ref t_terms),
                ) => if s_name == t_name && s_terms.len() == t_terms.len() {
                    for (s, t) in s_terms.iter().zip(t_terms) {
                        stack.push((s, t));
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
