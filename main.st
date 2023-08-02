type fib: u64 -> u64
fib(n) = if n==0 {
	1
} else {
	if n==1 {
		1
	} else {
		fib(n-1) + fib(n-2)
	}
}

type main: () -> u64
main() = fib(20)
