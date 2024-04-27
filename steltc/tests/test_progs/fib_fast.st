type fib : (n: u32, a: u32=1, b: u32=1) -> u32
fib(0, a, b) = a
fib(1, a, b) = b
fib(n, a, b) = fib(n-1, b, a+b)

type main: () -> u32
main() = fib(40)
