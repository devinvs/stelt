// builtin types
type bool = True | False

type maybe<a> = None | Some(a)

type list<a> = Nil | Cons(a, list<a>)

// builtin traits
trait Eq<a> {
    type eq: (a, a) -> bool
}

impl Eq for bool {
    eq(True, True) = True
    eq(False, False) = True
    eq(a, b) = False
}

impl Eq for maybe<Eq> {
    eq(Some(x), Some(y)) = eq(x, y)
    eq(None, None) = True
    eq(x, y) = False
}

impl Eq for list<Eq> {
    eq([], []) = True
    eq([], x) = False
    eq(x, []) = False
    eq(x::xs, y::ys) = eq(x, y) && eq(xs, ys)
}

trait Show<a> {
    type to_str: (a) -> str
}

impl Show for bool {
    show(True) = "True"
    show(False) = "False"
}

impl Show for maybe<Show> {
    show(None) = "None"
    show(Some(a)) = show(a)
}

trait Map<f> {
    type map: (f<a>, a->b) -> f<b>
}

impl Map for list {
    map([], f) = []
    map(x::xs, f) = f(x)::xs.map(f)
}

impl Map for maybe {
    map(None, f) = None
    map(Some(a), f) = Some(f(a))
}
