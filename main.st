type map<a, b>: (maybe<a>, a->b) -> maybe<b>
map(None, _) = None
map(Some(a), f) = Some(f(a))

type addtwo: i32 -> i32
addtwo(x) = x+2

type unwrap<a>: maybe<a> -> a
unwrap(Some(a)) = a

type main: () -> i32
main() = unwrap(map(Some(5), addtwo))
