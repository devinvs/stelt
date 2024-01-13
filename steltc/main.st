from prelude import add, list, char

sum: list<u32> -> u32
sum(l) = match l with [
	list.Nil -> 0,
	list.Cons(x, xs) -> x + sum(xs)
]

main : () -> u32
main() = sum([1, 2, 3, 4])
