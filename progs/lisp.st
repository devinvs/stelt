from prelude import char, eq

extern readline: str -> str
extern puts: str -> ()

print: str -> ()
print(s) = puts(s)

# a node in the ast is either an atom containing a string
# or a list containing a list of nodes
type ast = Atom(str) | List([ast])

# Since we check equality for the following types we need
# to implement the eq function for each of them.
# in the future I might want to automatically derive eq
# or have a derive keyword such as haskell or rust

# implement equals for our ast
impl eq(ast)
eq(ast.Atom(x), ast.Atom(y)) = x==y
eq(ast.List(xs), ast.List(ys)) = xs==ys
eq(_, _) = False

# implement equals for [ast]
impl eq([ast])
eq([], []) = True
eq(x::xs, y::ys) = x==y and xs==ys
eq(_, _) = False

read_string: () -> str
read_string() = readline("> ")

# parse the tree
# this is just a wrapper around our helper function since
# for the first parse call we don't care about how many
# tokens are left (for now at least)
parse: str -> ast
parse(input) = let (ast, _) = parse_h(input) in ast

# Parse the tree and return the ast and the remaining tokens
# Does the majority of the work with 3 cases:
# - ( goes to parse a list
# - ' executes the quote macro
# - else just parse as an atom
parse_h: str -> (ast, str)
parse_h(char.Char(40)::xs) =  let (asts, input) = parse_list(xs) in (ast.List(asts), input)
parse_h(char.Char(39)::xs) = 
	let (rest, xs) = parse_h(xs) in
	(ast.List([ast.Atom("quote"), rest]), xs)
parse_h(xs) = let (atom, input) = parse_atom(xs) in (ast.Atom(atom), input)

# Parse a list of tokens stopping at ) and skipping whitespace
# ( has already been popped so we just parse until )
parse_list: str -> ([ast], str)
parse_list(char.Char(41)::xs) = ([], xs) 			# stop at )
parse_list(char.Char(32)::xs) = parse_list(xs) 	# skip spaces
parse_list(char.Char(10)::xs) = parse_list(xs)		# skip newlines
parse_list(xs) =    					# continuously parse atoms
	let (first, xs) = parse_h(xs) in
	let (rest, xs) = parse_list(xs) in
	(first::rest, xs)

# Parse an atom
parse_atom: str -> (str, str)
parse_atom([]) = ([], [])
parse_atom(char.Char(x)::xs) = {
	if x!=40 and x!=41 and x>=33 and x<=126 then
		let (atom, xs) = parse_atom(xs) in
		(char.Char(x)::atom, xs)
	else
		([], char.Char(x)::xs)
}

# Print out a formatted ast
print_tree: ast -> ()
print_tree(ast.Atom(s)) = print(s)
print_tree(ast.List(xs)) = {
	print("( ")
	print_list(xs)
	print(")")
}

# print out list of asts separated by spaces
print_list: [ast] -> ()
print_list([]) = ()
print_list(x::xs) = {
	print_tree(x)
	print(" ")
	print_list(xs)
}

# This is where the magic of the interpreter starts. If you haven't read
# Paul Graham's "roots of lisp" I would highly recommend you do so

# find an identifier in the environment and return its corresponding expression
lookup: ([(str, env)], str) -> ast
lookup([], s) = ast.Atom(s)
lookup((key, val)::rest, test) =
	if key==test then val else lookup(rest, test)

# Evaluate an expression and possibly modify the environment
# Has the following builtins:
# - x	: a standalone atom is looked up in the env
# - (quote expr) : return the expression without evaluating
# - (atom expr) : return t if expr evaluates to an atom, else ()
# - (eq a b) : return t if a and b are atoms and equal or the empty list, else ()
# - (car l) : return the first element of the list l
# - (cdr l) : return the tail of the list l
# - (cons x l) : return a new list with head x and tail l
# - (label a expr) : add a new entry in the env of (a, expr)
# - ((lambda args body) vals) : apply the lambda funtion with the vals replaced for args
#
# additionally we implement a macro type thing:
# (defun name args body) -> (label name (lambda args body))
eval: (ast, [(str, ast)]) -> (ast, [(str, ast)])
# an atom is replaced by a lookup in the env
eval(ast.Atom(e), env) = (lookup(env, e), env)
# quote just returns the ast verbatim
eval(ast.List(ast.Atom("quote")::arg::_), env) = (arg, env)
# atom returns t if ast is atom and f if not
eval(ast.List(ast.Atom("atom")::arg::_), env) =
	match eval(arg, env) with [
		(ast.Atom(_), env) -> (ast.Atom("t"), env),
		(_, env) -> (ast.List([]), env)
	]
# eq checks if two atoms are equal
eval(ast.List(ast.Atom("eq")::a::b::_), env) =
	let (a, env) = eval(a, env) in
	let (b, env) = eval(b, env) in
	match (a, b) with [
		(ast.Atom(x), ast.Atom(y)) ->
			if x==y then (ast.Atom("t"), env) else (ast.List([]), env),
		(ast.List([]), ast.List([])) ->
			(ast.Atom("t"), env),
		_ -> (ast.List([]), env)
	]
# car takes the first element out of the list
eval(ast.List(ast.Atom("car")::arg::_), env) =
	match eval(arg, env) with [
		(ast.List(x::xs), env) -> (x, env),
		(_, env) -> (ast.List([]), env)
	]
# cdr takes the tail of the list
eval(ast.List(ast.Atom("cdr")::arg::_), env) =
	match eval(arg, env) with [
		(ast.List(x::xs), env) -> (ast.List(xs), env),
 		_ -> (ast.List([]), env)
 	]
# cons constructs a new list
eval(ast.List(ast.Atom("cons")::item::list::_), env) =
	let (x, env) = eval(item, env) in
	let (ast.List(xs), env) = eval(list, env) in
	(ast.List(x::xs), env)
# cond finds the first condition that is true
# and then evaluates its corresponding expression
eval(ast.List(ast.Atom("cond")::rest), env) = eval_cond(rest, env)
# label just adds the expression to the env without evaluating
eval(ast.List(ast.Atom("label")::ast.Atom(name)::val::_), env) =
	(ast.List([]), (name, val)::env)
# lambda application
# add entries to the env for each (arg, val) pair
# evaluate the body
# returns the original env
eval(ast.List(ast.List(ast.Atom("lambda")::ast.List(args)::body::_)::vals), env) = 
	let newenv = evlist(args, vals, env) in
	let (out, _) = eval(body, newenv) in
	(out, env)
# defun macro, way easier to define functions now
eval(ast.List(ast.Atom("defun")::name::args::body::_), env) =
	let expr = 
		ast.List([
			ast.Atom("label"),
			name,
			ast.List([
				ast.Atom("lambda"),
				args,
				body
			])
		])
	in
		eval(expr, env)
# else lookup the function name and continue
eval(ast.List(f::rest), env) =
	let (f, env) = eval(f, env) in
	eval(ast.List(f::rest), env)
	

# evaulate each val and insert into the env
evlist: ([ast], [ast], [(str, ast)]) -> [(str, ast)]
evlist([], _, env) = env
evlist(ast.Atom(name)::args, val::vals, env) =
	let (val, env) = eval(val, env) in
	(name, val)::evlist(args,  vals, env)

# evaluate each condition, if it is t then evaluate its expression
# no base case for now since thats just an error and I don't want to
# bother rewriting everything to catch errors just yet, at least
# not until I have newtypes/type aliases figured out...
# I mean look at the type signatures, all these []([]32], ast)>
# should at minimum be [](]tr, ast)>, or even better just env
eval_cond: ([ast], [(str, ast)]) -> (ast, [(str, ast)])
eval_cond(ast.List(cond::expr::_)::rest, env) =
	let (cond, env) = eval(cond, env) in
	if cond == ast.Atom("t") then
		eval(expr, env)
	else
		eval_cond(rest, env)


# print out the environment, useful for debugging
print_env: [(str, ast)] -> ()
print_env([]) = print("end")
print_env((name, expr)::xs) = {
	print(name)
	print(" ")
	print_tree(expr)
	print("\n")
}


# read, evaluate, print, loop
repl: [(str, ast)] -> ()
repl(env) = {
	print("lisp > ")
	let input = read_string() in
	let ast = parse(input) in
	let (out, env) = eval(ast, env) in
	{
		print_tree(out)
		puts("\n\n")
		repl(env)
	}
}

main: () -> ()
main() = repl([])	# start with an empty environment
