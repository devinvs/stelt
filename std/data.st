typefn map(outer) = (outer<a>, a->b) -> outer<b>
typefn flatmap(outer) = (outer<a>, a->outer<b>) -> outer<a>
typefn fold(outer) = (outer<a>, (a, b) -> b, b) -> b

type linked_list<a> = Nil | Cons(a, list<a>)

impl map(linked_list)
map([], _) = []
map(x::xs, f) = f(x)::map(xs, f)

impl flatten(linked_list)
flatten([]) = []
flatten(x::xs) = x ++ flatten(xs)

impl flatmap(list)
flatmap(xs, f) = xs.map(f).flatten()

impl fold(list)
fold([], _, agg) = agg
fold(x::xs, f, agg) = fold(xs, f, f(x, agg))


// A maybe type represents 
type maybe<a> = None | Some(a)

impl map(maybe)
map(None, _) = None
map(Some(x), f) = Some(f(x))

impl flatten(maybe)
flatten(None) = None
flatten(Some(x)) = x

impl flatmap(maybe)
flatmap(None, _) = None
flatmap(Some(x), f) = f(x)

