extern type getchar: () -> i32
extern type putchar: i32 -> ()

type ast = Atom(list<i32>) | List(list<ast>)

// read a string from stdin
type read_string: () -> list<i32>
read_string() = {
	let x = getchar() in
	if x == -1 then
		[]
	else
		x::read_string()
}

type parse: list<i32> -> ast
parse(input) = let (ast, _) = parse_h(input) in ast

type parse_h: list<i32> -> (ast, list<i32>)
parse_h(40::xs) =  let (asts, input) = parse_list(xs) in (List(asts), input)
parse_h(xs) = let (atom, input) = parse_atom(xs) in (Atom(atom), input)

type parse_list: list<i32> -> (list<ast>, list<i32>)
parse_list(41::xs) = ([], xs) 			// stop at )
parse_list(32::xs) = parse_list(xs) 	// skip spaces
parse_list(10::xs) = parse_list(xs)		// skip newlines
parse_list(xs) =    					// continuously parse atoms
	let (first, xs) = parse_h(xs) in
	let (rest, xs) = parse_list(xs) in
	(first::rest, xs)

type parse_atom: list<i32> -> (list<i32>, list<i32>)
parse_atom([]) = ([], [])
parse_atom(x::xs) = {
	if x!=40 && x!=41 && x>=33 && x<=126 then
		let (atom, xs) = parse_atom(xs) in
		(x::atom, xs)
	else
		([], x::xs)
}


type print_tree: ast -> ()
print_tree(Atom(s)) = print_string(s)
print_tree(List(xs)) = {
	putchar(40)
	putchar(32)
	print_list(xs)
	putchar(41)
}

type print_list: list<ast> -> ()
print_list(Nil) = ()
print_list(x::xs) = {
	print_tree(x)
	putchar(32)
	print_list(xs)
}

type print_string: list<i32> -> ()
print_string([]) = ()
print_string(x::xs) = {
	putchar(x)
	print_string(xs)
}

type main: () -> i32
main() = {
	let input = read_string() in
	let ast = parse(input) in
	print_tree(ast)
	putchar(10)
	0
}
