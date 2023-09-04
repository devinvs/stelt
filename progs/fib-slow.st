type fib: i32 -> i32
fib(0) = 1
fib(1) = 1
fib(n) = fib(n-1) + fib(n-2)

type main: () -> i32
main() = fib(30)
