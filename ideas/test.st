// storage is not a type, and shouldn't be a type
// ptr -- cannot be constructed, primarily for ffi. 
// box -- store on the heap via allocator, track as linear type, free when out of scope
// rc  -- box with a reference counter, track as linear type, but clones are cheap
// gc  -- use garbage collector for allocation, not a linear type
// + for all of these custom allocators can be defined for each type, defaults to global
//
// should we support custom storage qualifiers?
// this actually might be useful for interfacing with other gc'ed langs
 
type list<a> = Nil | Cons(a, box list<a>)

type map<a, b>: (list<a>, a->b) -> list<b>
map([], _) = []
map(x::xs, f) = f(x)::map(xs, f)
// or
map(Cons(x, box xs)) = f(x)::map(xs, f)
// but not
map(Cons(x, xs)) = f(x)::map(xs, f)
// this will cause a type error since
// a != box a


// closures...
main() =
	let y = 5 in
	x -> x + y

// creates closure (lambda.0, box 5)
// can we create closure manually?

type shim: (box i32, i32) -> i32
shim(box y, x) = x + y

type f: (a->b, box i32)
f() = (shim, box 5)

map: (list<i32>, i32 -> )

// generator
// nums is a generator from n to infinity
type nums: i32 -> (i32, () -> i32)
nums(n) = (n, || -> nums(n+1))

main() =
	let gen = nums in
	let (a, gen) = gen() in
	let (b, gen) = gen() in
	let (c, gen) = gen() in
	a + b + c

// what if I implemented lexically scoped atoms...
type memoize<a, b>: (a -> b) -> (a -> b)
memoize(f) =
	let mem = atom() in
	|args| ->
		let Some(val) = find(mem, args) in
			val
		else f(args)


x -> x + 1
(x, y) -> x - y
((x, y) -> x < y)(5, 3)	// false

let f = x -> y -> x + y
let f = x -> (y -> x + y)
// f(5)(2) == 7
