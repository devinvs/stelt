typefn add(a) = (a, a) -> a
typefn zero(a) = () -> a
typefn eq(a) = (a, a) -> bool


type list<'a> = Nil | Cons('a, list<'a>)

unsafe sum: list<u32> -> u32
sum(l) = match l with [
	list.Nil -> test(l),
	list.Cons(x, xs) -> x + unsafe sum(xs)
]

test : list<u32> -> u32
test(_) = 0

