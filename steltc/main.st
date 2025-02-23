main: () -> u32
main() = sum(map([1, 2, 3, 4, 5], square))

square: u32 -> u32
square(x) = x*x

map: (['a], 'a -> 'b) -> ['b]
map([], _) = []
map(x::xs, f) = f(x)::map(xs, f)

sum: [u32] -> u32
sum([]) = 0
sum(x::xs) = x + sum(xs)
