extern type getchar: () -> i32
extern type putchar: i32 -> ()

// a node in the ast is either an atom containing a string
// or a list containing a list of nodes
type ast = Atom(list<i32>) | List(list<ast>)

// Since we check equality for the following types we need
// to implement the eq function for each of them.
// in the future I might want to automatically derive eq
// or have a derive keyword such as haskell or rust

// implement equals for a list of number
impl eq(list<i32>)
eq([], []) = True
eq([], bs) = False
eq(as, []) = False
eq(a::as, b::bs) = a==b && as==bs

// implement equals for our ast
impl eq(ast)
eq(Atom(x), Atom(y)) = x==y
eq(List(xs), List(ys)) = xs==ys
eq(_, _) = False

// implement equals for list<ast>
impl eq(list<ast>)
eq([], []) = True
eq(x::xs, y::ys) = x==y && xs==ys
eq(_, _) = False

// read a string from stding using getchar()
// stop at newline or EOF
type read_string: () -> list<i32>
read_string() = {
	let x = getchar() in
	if x == -1 || x == 10 then
		[]
	else
		x::read_string()
}


// parse the tree
// this is just a wrapper around our helper function since
// for the first parse call we don't care about how many
// tokens are left (for now at least)
type parse: list<i32> -> ast
parse(input) = let (ast, _) = parse_h(input) in ast

// Parse the tree and return the ast and the remaining tokens
// Does the majority of the work with 3 cases:
// - ( goes to parse a list
// - ' executes the quote macro
// - else just parse as an atom
type parse_h: list<i32> -> (ast, list<i32>)
parse_h(40::xs) =  let (asts, input) = parse_list(xs) in (List(asts), input)
parse_h(39::xs) = 
	let (rest, xs) = parse_h(xs) in
	(List([Atom("quote"), rest]), xs)
parse_h(xs) = let (atom, input) = parse_atom(xs) in (Atom(atom), input)

// Parse a list of tokens stopping at ) and skipping whitespace
// ( has already been popped so we just parse until )
type parse_list: list<i32> -> (list<ast>, list<i32>)
parse_list(41::xs) = ([], xs) 			// stop at )
parse_list(32::xs) = parse_list(xs) 	// skip spaces
parse_list(10::xs) = parse_list(xs)		// skip newlines
parse_list(xs) =    					// continuously parse atoms
	let (first, xs) = parse_h(xs) in
	let (rest, xs) = parse_list(xs) in
	(first::rest, xs)

// Parse an atom
type parse_atom: list<i32> -> (list<i32>, list<i32>)
parse_atom([]) = ([], [])
parse_atom(x::xs) = {
	if x!=40 && x!=41 && x>=33 && x<=126 then
		let (atom, xs) = parse_atom(xs) in
		(x::atom, xs)
	else
		([], x::xs)
}

// Print out a formatted ast
type print_tree: ast -> ()
print_tree(Atom(s)) = print_string(s)
print_tree(List(xs)) = {
	putchar(40)
	putchar(32)
	print_list(xs)
	putchar(41)
}

// print out list of asts separated by spaces
type print_list: list<ast> -> ()
print_list(Nil) = ()
print_list(x::xs) = {
	print_tree(x)
	putchar(32)
	print_list(xs)
}

// print out a string
type print_string: list<i32> -> ()
print_string([]) = ()
print_string(x::xs) = {
	putchar(x)
	print_string(xs)
}

// This is where the magic of the interpreter starts. If you haven't read
// Paul Graham's "roots of lisp" I would highly recommend you do so

// find an identifier in the environment and return its corresponding expression
type lookup: (list<(list<i32>, ast)>, list<i32>) -> ast
lookup([], s) = Atom(s)
lookup((key, val)::rest, test) =
	if key==test then val else lookup(rest, test)

// Evaluate an expression and possibly modify the environment
// Has the following builtins:
// - x	: a standalone atom is looked up in the env
// - (quote expr) : return the expression without evaluating
// - (atom expr) : return t if expr evaluates to an atom, else ()
// - (eq a b) : return t if a and b are atoms and equal or the empty list, else ()
// - (car l) : return the first element of the list l
// - (cdr l) : return the tail of the list l
// - (cons x l) : return a new list with head x and tail l
// - (label a expr) : add a new entry in the env of (a, expr)
// - ((lambda args body) vals) : apply the lambda funtion with the vals replaced for args
//
// additionally we implement a macro type thing:
// (defun name args body) -> (label name (lambda args body))
type eval: (ast, list<(list<i32>, ast)>) -> (ast, list<(list<i32>, ast)>)
// an atom is replaced by a lookup in the env
eval(Atom(e), env) = (lookup(env, e), env)
// quote just returns the ast verbatim
eval(List(Atom("quote")::arg::_), env) = (arg, env)
// atom returns t if ast is atom and f if not
eval(List(Atom("atom")::arg::_), env) =
	match eval(arg, env) {
		(Atom(_), env): (Atom("t"), env),
		(_, env): (List([]), env)
	}
// eq checks if two atoms are equal
eval(List(Atom("eq")::a::b::_), env) =
	let (a, env) = eval(a, env) in
	let (b, env) = eval(b, env) in
	match (a, b) {
		(Atom(x), Atom(y)):
			if x==y then (Atom("t"), env) else (List([]), env),
		(List([]), List([])):
			(Atom("t"), env),
		_:
			(List([]), env)
	}
// car takes the first element out of the list
eval(List(Atom("car")::arg::_), env) =
	match eval(arg, env) {
		(List(x::xs), env): (x, env),
		(_, env): (List([]), env)
	}
// cdr takes the tail of the list
eval(List(Atom("cdr")::arg::_), env) =
	match eval(arg, env) {
		(List(x::xs), env): (List(xs), env),
 		_: (List([]), env)
 	}
// cons constructs a new list
eval(List(Atom("cons")::item::list::_), env) =
	let (x, env) = eval(item, env) in
	let (List(xs), env) = eval(list, env) in
	(List(x::xs), env)
// cond finds the first condition that is true
// and then evaluates its corresponding expression
eval(List(Atom("cond")::rest), env) = eval_cond(rest, env)
// label just adds the expression to the env without evaluating
eval(List(Atom("label")::Atom(name)::val::_), env) =
	(List([]), Cons((name, val), env))
// lambda application
// add entries to the env for each (arg, val) pair
// evaluate the body
// returns the original env
eval(List(List(Atom("lambda")::List(args)::body::_)::vals), env) = 
	let newenv = evlist(args, vals, env) in
	let (out, _) = eval(body, newenv) in
	(out, env)
// defun macro, way easier to define functions now
eval(List(Atom("defun")::name::args::body::_), env) =
	let expr = 
		List([
			Atom("label"),
			name,
			List([
				Atom("lambda"),
				args,
				body
			])
		])
	in
		eval(expr, env)
// else lookup the function name and continue
eval(List(f::rest), env) =
	let (f, env) = eval(f, env) in
	eval(List(f::rest), env)
	

// evaulate each val and insert into the env
type evlist: (list<ast>, list<ast>, list<(list<i32>, ast)>) -> list<(list<i32>, ast)>
evlist([], _, env) = env
evlist(Atom(name)::args, val::vals, env) =
	let (val, env) = eval(val, env) in
	(name, val)::evlist(args,  vals, env)

// evaluate each condition, if it is t then evaluate its expression
// no base case for now since thats just an error and I don't want to
// bother rewriting everything to catch errors just yet, at least
// not until I have newtypes/type aliases figured out...
// I mean look at the type signatures, all these list<(list<i32>, ast)>
// should at minimum be list<(str, ast)>, or even better just env
type eval_cond: (list<ast>, list<(list<i32>, ast)>) -> (ast, list<(list<i32>, ast)>)
eval_cond(List(cond::expr::_)::rest, env) =
	let (cond, env) = eval(cond, env) in
	if cond == Atom("t") then
		eval(expr, env)
	else
		eval_cond(rest, env)


// print out the environment, useful for debugging
type print_env: list<(list<i32>, ast)> -> ()
print_env([]) = print_string("end")
print_env((name, expr)::xs) = {
	print_string(name)
	putchar(32)
	print_tree(expr)
	putchar(10)
}


// read, evaluate, print, loop
type repl: (list<(list<i32>, ast)>) -> ()
repl(env) = {
	print_string("lisp > ")
	let input = read_string() in
	let ast = parse(input) in
	let (out, env) = eval(ast, env) in
	{
		print_tree(out)
		putchar(10)
		putchar(10)
		repl(env)
	}
}

type main: () -> ()
main() =
	repl([])	// start with an empty environment
