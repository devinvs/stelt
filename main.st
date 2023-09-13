type map<a, b>: (list<a>, a->b) -> list<b>
map([], _) = []
map(x::xs, f) = Cons(f(x), map(xs, f))

type sum: list<u32> -> u32
sum([]) = 0
sum(x::xs) = x + sum(xs)

type square: u32 -> u32
square(x) = x * x

type main: () -> u32
main() = sum(map([1, 2, 3, 4], square))
