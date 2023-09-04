type fib: i32 -> i32
fib(n) = fib_h(1, 1, n)

type fib_h: (i32, i32, i32) -> i32
fib_h(a, b, 0) = a
fib_h(a, b, 1) = b
fib_h(a, b, n) = fib_h(b, a+b, n-1)

type main: () -> i32
main() = fib(30)
