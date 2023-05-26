extern type putchar: i32 -> ()

type putd: i32 -> ()
putd(x) = putchar(x+48)

type putnum: i32 -> ()
putnum(0) = putd(0)
putnum(x) = putnum_h(x)

type putnum_h: i32 -> ()
putnum_h(0) = ()
putnum_h(n) = {
    putnum_h(n / 10)
    putd(n % 10)
}

type fib: i32 -> i32
fib(0) = 1
fib(1) = 1
fib(n) = fib(n-1) + fib(n-2)

type main: () -> ()
main() = putnum(fib(40))
