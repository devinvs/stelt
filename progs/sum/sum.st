type sum: [i32] -> i32
sum([]) = 0
sum(x::xs) = x + sum(xs)

type main: () -> i32
main() = sum([5, 10, 12, 7, 2, 3, 0])
