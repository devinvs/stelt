typefn map(outer) = (outer<a>, a->b) -> outer<b>
typefn flatten(outer) = outer<outer<a>> -> outer<a>
typefn flatmap(outer) = (outer<a>, a->outer<b>) -> outer<a>

// Iterator operations
typefn next(iter, a) = iter -> maybe<(a, iter)>

type list<a> = Nil | Cons(a, list<a>)

impl next(list<a>, a)
next([]) = None
next(x::xs) = Some((x, xs))

impl filter(list)
filter([], _) = []
filter(x::xs, f) = if f(x) then x::rest else rest
	where rest = filter(xs, f)

impl map(list)
map([], _) = []
map(x::xs, f) = f(x)::map(xs, f)

impl flatten(list)
flatten([]) = []
flatten(x::xs) = x ++ flatten(xs)

impl flatmap(list)
flatmap(xs, f) = xs.map(f).flatten()


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
