typefn add(a) = (a, a) -> a
typefn zero(a) = () -> a
typefn eq(a) = (a, a) -> bool


type list<'a> = Nil | Cons('a, list<'a>)

type sum: add('a) + zero('a) => list<'a> -> 'a
sum(list.Nil) = zero()
sum(list.Cons(x, xs)) = x + sum(xs)
