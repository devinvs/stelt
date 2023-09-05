typefn next(iter, a) = iter -> (a, iter)

type range = Range(i32, i32)

impl next(range, maybe<i32>)
next(Range(n, m)) =
	if n==m then
		(None, Range(n, m))
	else
		(Some(n), Range(n+1, m))

type rangesum<a>: a -> i32
rangesum(i) =
	let (res, i) = next(i) in
	match res {
		None: 0,
		Some(n): n+rangesum(i)
	}

type main: () -> i32
main() = rangesum(Range(5, 8))
