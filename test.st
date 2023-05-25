//extern type puts: str -> i32

type fact: i32 -> i32
fact(0) = 1
fact(n) = n*fact(n-1)

type main: () -> i32
main() = fact(5)
