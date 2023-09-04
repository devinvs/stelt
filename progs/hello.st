extern type putchar: i32 -> ()

type print: list<i32> -> ()
print([]) = ()
print(x::xs) = {
	putchar(x)
	print(xs)
}

type main: () -> ()
main() = print("hello world\n")

