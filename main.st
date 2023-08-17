extern type getchar: () -> i32
extern type putchar: i32 -> ()

type ast = Atom(list<i32>) | List(list<ast>)

impl eq(list<i32>)
eq([], []) = True
eq([], _) = False
eq(_, []) = False
eq(a::as, b::bs) = a==b && as==bs

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
parse_h(xxs) = let (atom, ninput) = parse_atom(xxs) in (Atom(atom), ninput)

type parse_list: list<i32> -> (list<ast>, list<i32>)
parse_list(41::xs) = ([], xs) 			// stop at )
parse_list(32::xxs) = parse_list(xxs) 	// skip spaces
parse_list(10::xxxs) = parse_list(xxxs)		// skip newlines
parse_list(ys) =    					// continuously parse atoms
	let (first, zs) = parse_h(ys) in
	let (rest, as) = parse_list(zs) in
	(first::rest, as)

type parse_atom: list<i32> -> (list<i32>, list<i32>)
parse_atom([]) = ([], [])
parse_atom(x::xs) = {
	if x!=40 && x!=41 && x>=33 && x<=126 then
		let (atom, newxs) = parse_atom(xs) in
		(x::atom, newxs)
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

type lookup: (list<(list<i32>, ast)>, list<i32>) -> ast
lookup([], s) = Atom(s)
lookup((key, val)::rest, test) =
	if key==test then val else lookup(rest, test)

// type first<a>: list<a> -> a
// first(x::xs) = x

// type rest<a>: list<a> -> list<a>
// rest(x::xs) = xs

type eval: (ast, list<(list<i32>, ast)>) -> (ast, list<(list<i32>, ast)>)
// an atom is replaced by a lookup in the env
eval(Atom(e), q) = (lookup(q, e), q)
// quote just returns the ast verbatim
// eval(List(Atom("quote")::arg::_), env) = (arg, env)
// atom returns t if ast is atom and f if not
eval(List(Atom("atom")::arg::_), y) =
	match eval(arg, y) {
		(Atom(_), newenva): (Atom("t"), newenva),
		(_, newenv): (Atom("f"), newenv)
	}
// eq checks if two atoms are equal
eval(List(Atom("eq")::a::b::_), env) =
	let (newa, aenv) = eval(a, env) in
	let (newb, benv) = eval(b, aenv) in
	match (newa, newb) {
		(Atom(x), Atom(r)):
			if x==r then (Atom("t"), benv) else (Atom("f"), benv),
		_:
			(Atom("f"), benv)
	}
	
// eval(List(Atom("car")::arg::_), env) =
// 	match eval(arg) {
// 		List(xs): first(xs),
// 		_: Atom("f")
// 	}
// eval(List(Atom("cdr")::arg::_), env) =
// 	match eval(arg) {
// 		List(xs): rest(xs),
// 		_: Atom("f")
// 	}
// eval(List(Atom("cons")::item::list::_)) =
	// let (x, List(xs)) = (eval(item), eval(list)) in
	// List(x::xs)
// eval(List(Atom("cond")::rest)) = eval_cond(rest, env)

// type repl: (list<(list<i32>, ast)>) -> ()
// repl(env) = {
// 	let input = read_string() in
// 	{
// 		print_string(input)
// 		let ast = parse(input) in
// 		{
// 			print_tree(ast)
// 			putchar(10)
// 			let (out, env) = eval(ast, env) in
// 			print_tree(out)
// 			repl(env)
// 		}
// 	}
// }

type main: () -> ()
main() =
	let input = read_string() in
	{
		print_string(input)
		let ast = parse(input) in
			let (out, env) = eval(ast, []) in
			{
				print_tree(out)
				putchar(10)
			}
	}
