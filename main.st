import print

extern type puts: str -> ()

type List<a> = Nil | Cons(a, List<a>)

type sum: List<i32> -> i32
sum(Nil) = 0
sum(Cons(x, xs)) = x + sum(xs)

type main: () -> ()
main() = {
    print.putd(sum(Cons(5, Nil)))
    puts("hello world")
}
