type sum: [i32] -> i32
sum([]) = 0
sum(x::xs) = x + sum(xs)

type map: (['a], 'a -> 'b) -> ['b]
map([], _) = []
map(x::xs, f) = f(x)::map(xs, f)

type main: () -> i32
main() = sum(map(x -> x*x, [1, 2, 3, 4, 5]))

