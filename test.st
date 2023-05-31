type test: i32 -> i32
test(x) = {
    let f = (y) -> x*x*y
    f(2)
}

type main: () -> i32
main() = test(3)
