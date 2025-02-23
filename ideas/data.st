main : io<()>
main =
	f <- open("file.txt").await() in
	l <- f.lines().for_each() in
	match l.split(" ").get(3).map(parse_u64) with [
		maybe.Some(result.Ok(n)) -> when(n>6, println),
		_ -> yield()
	]
