type Bool = False | True
type Maybe<a> = None | Some(a)
type List<a> = Nil | Cons(a, List<a>)

// The llvm macro is handled specially by the compiler.
// In place of the expression the compiler will inject the
// llvm string verbatim
//
// Takes the output variable name and the llvm body
type llvm!<a> : (str, str) -> a


type add: (i32, i32) -> i32
add(a, b) = llvm!("%out", "%out = add i32 %anon.1, %anon.2")

type sub: (i32, i32) -> i32
sub(a, b) = llvm!("%out", "%out = sub i32 %anon.1, %anon.2")

type mul: (i32, i32) -> i32
mul(a, b) = llvm!("%out", "%out = mul i32 %anon.1, %anon.2")

type div: (i32, i32) -> i32
div(a, b) = llvm!("%out", "%out = sdiv i32 %anon.1, %anon.2")

type mod: (i32, i32) -> i32
mod(a, b) = llvm!("%out", "%out = srem i32 %anon.1, %anon.2")

type eq: (i32, i32) -> Bool
eq(a, b) = llvm!(
	"%out",
	"
%cmp = icmp eq i32 %anon.1, %anon.2
%cast = zext i1 %cmp to i8
%out = insertvalue %Bool undef, i8 %cast, 0
	"
)


// I hate this and this will definitely be removed later
// also will probably be replaced with buffer type
// wow this is a mess
extern type malloc: i32 -> str
