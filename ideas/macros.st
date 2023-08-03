// A macro is a function which runs at compile time on the program tree
// It must end in an exclamation point
// It must return a single ast node

// A macro which replaces all '+' with '-'
type sub_minus!: ast.Expr -> ast.Expr
sub_minus!(ast.Add(a, b)) = ast.Sub(a, b)
sub_minus!(other) = ast.visit(other, sub_minus!)

type tricky: (i32, i32) -> i32
tricky(a, b) = sub_minus!(a + b)

test tricky(5, 2) == 3

// this makes compiling code soooooo much harder.
// In order to get the parse tree, we need the parse tree
// probably need to implement lisp-like interpreter...
// may be useful for repl in the future though
