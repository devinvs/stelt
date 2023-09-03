typefn map<a, b>(f) = (f<a>, a->b) -> f<b>

impl map(maybe)
map(None, _) = None
map(Some(a), f) = Some(f(a))

type unwrap<a>: maybe<a> -> a
unwrap(Some(a)) = a

type add_two: i32 -> i32
add_two(x) = x+2

type main: () -> i32
main() = unwrap(map(Some(2), add_two))
