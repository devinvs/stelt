type Bool = False | True
type Maybe<a> = None | Some(a)
type List<a> = Nil | Cons(a, List<a>)

// The llvm macro is handled specially by the compiler.
// In place of the expression the compiler will inject the
// llvm string verbatim
//
// Takes the output variable name and the llvm body
type llvm!<a> : (str, str) -> a


//
// Here lies the math spam. This is what I get for having so many int types
//

// Add
typefn add(a) = (a, a) -> a

impl add(u8)
add(a, b) = llvm!("%out", "%out = add i8 %anon.1, %anon.2")

impl add(i8)
add(a, b) = llvm!("%out", "%out = add i8 %anon.1, %anon.2")

impl add(u16)
add(a, b) = llvm!("%out", "%out = add i16 %anon.1, %anon.2")

impl add(i16)
add(a, b) = llvm!("%out", "%out = add i16 %anon.1, %anon.2")

impl add(u32)
add(a, b) = llvm!("%out", "%out = add i32 %anon.1, %anon.2")

impl add(i32)
add(a, b) = llvm!("%out", "%out = add i32 %anon.1, %anon.2")

impl add(u64)
add(a, b) = llvm!("%out", "%out = add i64 %anon.1, %anon.2")

impl add(i64)
add(a, b) = llvm!("%out", "%out = add i64 %anon.1, %anon.2")

// Sub
typefn sub(a) = (a, a) -> a

impl sub(u8)
sub(a, b) = llvm!("%out", "%out = sub i8 %anon.1, %anon.2")

impl sub(i8)
sub(a, b) = llvm!("%out", "%out = sub i8 %anon.1, %anon.2")

impl sub(u16)
sub(a, b) = llvm!("%out", "%out = sub i16 %anon.1, %anon.2")

impl sub(i16)
sub(a, b) = llvm!("%out", "%out = sub i16 %anon.1, %anon.2")

impl sub(u32)
sub(a, b) = llvm!("%out", "%out = sub i32 %anon.1, %anon.2")

impl sub(i32)
sub(a, b) = llvm!("%out", "%out = sub i32 %anon.1, %anon.2")

impl sub(u64)
sub(a, b) = llvm!("%out", "%out = sub i64 %anon.1, %anon.2")

impl sub(i64)
sub(a, b) = llvm!("%out", "%out = sub i64 %anon.1, %anon.2")

// Mul
typefn mul(a) = (a, a) -> a

impl mul(u8)
mul(a, b) = llvm!("%out", "%out = mul i8 %anon.1, %anon.2")

impl mul(i8)
mul(a, b) = llvm!("%out", "%out = mul i8 %anon.1, %anon.2")

impl mul(u16)
mul(a, b) = llvm!("%out", "%out = mul i16 %anon.1, %anon.2")

impl mul(i16)
mul(a, b) = llvm!("%out", "%out = mul i16 %anon.1, %anon.2")

impl mul(u32)
mul(a, b) = llvm!("%out", "%out = mul i32 %anon.1, %anon.2")

impl mul(i32)
mul(a, b) = llvm!("%out", "%out = mul i32 %anon.1, %anon.2")

impl mul(u64)
mul(a, b) = llvm!("%out", "%out = mul i64 %anon.1, %anon.2")

impl mul(i64)
mul(a, b) = llvm!("%out", "%out = mul i64 %anon.1, %anon.2")

// Div
typefn div(a) = (a, a) -> a

impl div(u8)
div(a, b) = llvm!("%out", "%out = sdiv i8 %anon.1, %anon.2")

impl div(i8)
div(a, b) = llvm!("%out", "%out = sdiv i8 %anon.1, %anon.2")

impl div(u16)
div(a, b) = llvm!("%out", "%out = sdiv i16 %anon.1, %anon.2")

impl div(i16)
div(a, b) = llvm!("%out", "%out = sdiv i16 %anon.1, %anon.2")

impl div(u32)
div(a, b) = llvm!("%out", "%out = sdiv i32 %anon.1, %anon.2")

impl div(i32)
div(a, b) = llvm!("%out", "%out = sdiv i32 %anon.1, %anon.2")

impl div(u64)
div(a, b) = llvm!("%out", "%out = sdiv i64 %anon.1, %anon.2")

impl div(i64)
div(a, b) = llvm!("%out", "%out = sdiv i64 %anon.1, %anon.2")

// Mod
typefn mod(a) = (a, a) -> a

impl mod(u8)
mod(a, b) = llvm!("%out", "%out = srem i8 %anon.1, %anon.2")

impl mod(i8)
mod(a, b) = llvm!("%out", "%out = srem i8 %anon.1, %anon.2")

impl mod(u16)
mod(a, b) = llvm!("%out", "%out = srem i16 %anon.1, %anon.2")

impl mod(i16)
mod(a, b) = llvm!("%out", "%out = srem i16 %anon.1, %anon.2")

impl mod(u32)
mod(a, b) = llvm!("%out", "%out = srem i32 %anon.1, %anon.2")

impl mod(i32)
mod(a, b) = llvm!("%out", "%out = srem i32 %anon.1, %anon.2")

impl mod(u64)
mod(a, b) = llvm!("%out", "%out = srem i64 %anon.1, %anon.2")

impl mod(i64)
mod(a, b) = llvm!("%out", "%out = srem i64 %anon.1, %anon.2")


typefn eq(a) = (a, a) -> Bool

impl eq(u8)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i8 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %Bool undef, i8 %cast, 0")

impl eq(i8)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i8 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %Bool undef, i8 %cast, 0")

impl eq(u16)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i16 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %Bool undef, i8 %cast, 0")

impl eq(i16)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i16 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %Bool undef, i8 %cast, 0")

impl eq(u32)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i32 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %Bool undef, i8 %cast, 0")

impl eq(i32)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i32 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %Bool undef, i8 %cast, 0")

impl eq(u64)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i64 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %Bool undef, i8 %cast, 0")

impl eq(u64)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i64 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %Bool undef, i8 %cast, 0")

// I hate this and this will definitely be removed later
// also will probably be replaced with buffer type
// wow this is a mess
extern type malloc: i32 -> str
