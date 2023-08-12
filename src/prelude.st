type bool = False | True
type maybe<a> = None | Some(a)
type list<a> = Nil | Cons(a, list<a>)

//
// Here lies the math spam. This is what I get for having so many int types
//

type not: bool -> bool
not(True) = False
not(False) = True

type and: (bool, bool) -> bool
and(True, True) = True
and(_, _) = False

// Neg
typefn neg(a) = a -> a

impl neg(i8)
neg(a) = llvm!("%out", "%out = mul i8 %arg.0, -1")

impl neg(i16)
neg(a) = llvm!("%out", "%out = mul i16 %arg.0, -1")

impl neg(i32)
neg(a) = llvm!("%out", "%out = mul i32 %arg.0, -1")

impl neg(i64)
neg(a) = llvm!("%out", "%out = mul i64 %arg.0, -1")

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


typefn eq(a) = (a, a) -> bool

type neq<a>: (a, a) -> bool
neq(a, b) = !eq(a, b)

impl eq(u8)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i8 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl eq(i8)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i8 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl eq(u16)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i16 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl eq(i16)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i16 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl eq(u32)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i32 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl eq(i32)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i32 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl eq(u64)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i64 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl eq(i64)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i64 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

typefn geq(a) = (a, a) -> bool

impl geq(i8)
geq(a, b) = llvm!(
	"%out", "
	%cmp = icmp sge i8 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl geq(u8)
geq(a, b) = llvm!(
	"%out", "
	%cmp = icmp uge i8 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl geq(i16)
geq(a, b) = llvm!(
	"%out", "
	%cmp = icmp sge i16 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl geq(u16)
geq(a, b) = llvm!(
	"%out", "
	%cmp = icmp uge i16 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl geq(i32)
geq(a, b) = llvm!(
	"%out", "
	%cmp = icmp sge i32 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl geq(u32)
geq(a, b) = llvm!(
	"%out", "
	%cmp = icmp uge i32 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl geq(i64)
geq(a, b) = llvm!(
	"%out", "
	%cmp = icmp sge i64 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl geq(u64)
geq(a, b) = llvm!(
	"%out", "
	%cmp = icmp uge i64 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

typefn leq(a) = (a, a) -> bool

impl leq(i8)
leq(a, b) = llvm!(
	"%out", "
	%cmp = icmp sle i8 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl leq(u8)
leq(a, b) = llvm!(
	"%out", "
	%cmp = icmp ule i8 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl leq(i16)
leq(a, b) = llvm!(
	"%out", "
	%cmp = icmp sle i16 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl leq(u16)
leq(a, b) = llvm!(
	"%out", "
	%cmp = icmp ule i16 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl leq(i32)
leq(a, b) = llvm!(
	"%out", "
	%cmp = icmp sle i32 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl leq(u32)
leq(a, b) = llvm!(
	"%out", "
	%cmp = icmp ule i32 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl leq(i64)
leq(a, b) = llvm!(
	"%out", "
	%cmp = icmp sle i64 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl leq(u64)
leq(a, b) = llvm!(
	"%out", "
	%cmp = icmp ule i64 %anon.1, %anon.2
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

// I hate this and this will definitely be removed later
// also will probably be replaced with buffer type
// wow this is a mess
extern type malloc: i32 -> str
