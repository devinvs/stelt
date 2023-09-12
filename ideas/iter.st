// an iterator is just defined as something that you can
// get the next element from, also returning an iterator
// for getting future elements
typefn next(iter, a) = iter -> (a, iter)

// next can be implmeneted trivially for a list without
// storing any state beyond just the list itself
impl next<a>(list<a>, maybe<a>)
next([]) = (None, [])
next(x::xs) = (Some(x), xs)

// an iterator that repeats a single number forever
// is maybe not super useful but it is easy to define
type repeat = Repeat(i32)

impl next(repeat, i32)
next(Repeat(n)) = (n, Repeat(n))

// slightly more complicated we can create an iterator
// for all the natural numbers
type naturals = Naturals(u32)

impl next(naturals, u32)
next(Naturals(n)) = (n, Naturals(n+1))

// or we can define an iterator that returns numbers
// between a given range [n..m)
type range = Range(i32, i32)

impl next(range, maybe<i32>)
next(Range(n, m)) =
	if n==m then
		(None, Range(n, m))
	else
		(Some(n), Range(n+1, m))

type skip<iter>: (iter, i32) -> iter
skip(iter, 0) = iter
skip(iter, n) = let (_, iter) = next(iter) in skip(iter, n-1)

// utility functions can be built on these primitives
type nth<iter, out>: (iter, i32) -> out
nth(iter, n) = let (out, _) = next(skip(iter, n)) in out

// defining the fibonacci sequence
// as an iterator intuitively brings us to the dynamic
// program solution (as opposed to the slow naive one)
type fib = Fib(i32, i32)

impl next(fib, i32)
next(Fib(a, b)) = (a, Fib(b, a+b))

type fibs: () -> fib
fibs() = Fib(1, 1)

type lucas: () -> fib
lucas() = fib(1, 2)

// get the 30th fibonacci number
type main: () -> i32
main() = nth(fibs(), 30)
