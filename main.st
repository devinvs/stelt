
type list<a> = Nil | Cons(a, list<a>)
type maybe<a> = None | Some(a)

typefn map<p, q>(f) = (f<p>, p->q) -> f<q>

impl map(maybe)
map(None, f) = None
map(Some(a), f) = Some(f(a))

impl map(list)
map(x::xs, f) = f(x)::map(xs, f)
map([], f) = []
