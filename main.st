type map<a, b>: (list<a>, a->b) -> list<b>
map([], _) = []
map(x::xs, f) = Cons(f(x), map(xs, f))

type sum: list<u32> -> u32
sum([]) = 0
sum(x::xs) = x + sum(xs)

type square: u32 -> u32
square(x) = x * x

type mul_by: u32 -> (u32 -> u32)
mul_by(y) = (x) -> x*y

type main: () -> u32
main() = 
	let f = mul_by(2) in
	let l = [1, 2, 3, 4] in
	sum(map(l, f))
