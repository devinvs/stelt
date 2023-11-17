typefn add(a) = (a, a) -> a
typefn zero(a) = () -> a
typefn eq(a) = (a, a) -> bool


type list<'a> = Nil | Cons('a, list<'a>)

// sum: add('a) + zero('a) => list<'a> -> 'a
sum : a -> b
sum(l) = match l with [
	list.Nil -> zero(),
	list.Cons(x, xs) -> x+sum(xs)
]
