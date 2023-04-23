type fib: u64 -> u64
fib(0) = 1
fib(1) = 1
fib(x) = fib(x-1) + fib(x-2)

type main: () -> u64
main() = fib(7)
