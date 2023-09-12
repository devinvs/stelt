type map<a, b>: (maybe<a>, a->b) -> maybe<b>
map(None, _) = None
map(Some(a), f) = Some(f(a))

type unwrap<a>: maybe<a> -> a
unwrap(Some(a)) = a

type main: () -> i32
main() =
	let y = 5 in
	unwrap(map(Some(5), (x)->x+y))
