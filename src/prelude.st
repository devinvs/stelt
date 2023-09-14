// a boolean value, either false or true
// by specifying False first it will be equivalent to 0 and thus play nice
// with other languages
type bool = False | True

// a character is a 32bit integer.
// this allows for representing all unicode code points
// it is represented as a new type since not all integers are valid chars
type char = Char(u32)

// maybe is for a result that is something or nothing.
// it will eventually have some special optimizations, specifically
// a maybe<ptr> will use NULL for the None case (saving the 8 bit tag)
type maybe<a> = None | Some(a)

// A recursive linked list, in all its glory
type list<a> = Nil | Cons(a, list<a>)

// It's pretty cool that we can define logic entirely in the lang
// let's just hope it gets optimized

type not: bool -> bool
not(True) = False
not(False) = True

type and: (bool, bool) -> bool
and(True, True) = True
and(_, _) = False

type or: (bool, bool) -> bool
or(False, False) = False
or(_, _) = True

type xor: (bool, bool) -> bool
xor(True, False) = True
xor(False, True) = True
xor(_, _) = False

// an iterator is defined simply as just having being able to retreive the next element
typefn next(iter, out) = iter -> (out, iter)

type skip<iter>: (iter, u32) -> iter
skip(iter, 0) = iter
skip(iter, n) = let (_, iter) = next(iter) in skip(iter, n-1)

type take<iter, out>: (iter, u32) -> (list<out>, iter)
take(iter, 0) = ([], iter)
take(iter, n) =
	let (v, iter) = next(iter) in
	let (list, iter) = take(iter, n-1) in
	(v::list, iter)

type nth<iter, out>: (iter, u32) -> out
nth(iter, n) = let (out, _) = next(skip(iter, n)) in out

//
// Here lies the math spam. This is what I get for having so many int types
//

// maybe macros will fix this eventually, sigh

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
add(a, b) = llvm!("%out", "%out = add i8 %a, %b")

impl add(i8)
add(a, b) = llvm!("%out", "%out = add i8 %a, %b")

impl add(u16)
add(a, b) = llvm!("%out", "%out = add i16 %a, %b")

impl add(i16)
add(a, b) = llvm!("%out", "%out = add i16 %a, %b")

impl add(u32)
add(a, b) = llvm!("%out", "%out = add i32 %a, %b")

impl add(i32)
add(a, b) = llvm!("%out", "%out = add i32 %a, %b")

impl add(u64)
add(a, b) = llvm!("%out", "%out = add i64 %a, %b")

impl add(i64)
add(a, b) = llvm!("%out", "%out = add i64 %a, %b")

// Sub
typefn sub(a) = (a, a) -> a

impl sub(u8)
sub(a, b) = llvm!("%out", "%out = sub i8 %a, %b")

impl sub(i8)
sub(a, b) = llvm!("%out", "%out = sub i8 %a, %b")

impl sub(u16)
sub(a, b) = llvm!("%out", "%out = sub i16 %a, %b")

impl sub(i16)
sub(a, b) = llvm!("%out", "%out = sub i16 %a, %b")

impl sub(u32)
sub(a, b) = llvm!("%out", "%out = sub i32 %a, %b")

impl sub(i32)
sub(a, b) = llvm!("%out", "%out = sub i32 %a, %b")

impl sub(u64)
sub(a, b) = llvm!("%out", "%out = sub i64 %a, %b")

impl sub(i64)
sub(a, b) = llvm!("%out", "%out = sub i64 %a, %b")

// Mul
typefn mul(a) = (a, a) -> a

impl mul(u8)
mul(a, b) = llvm!("%out", "%out = mul i8 %a, %b")

impl mul(i8)
mul(a, b) = llvm!("%out", "%out = mul i8 %a, %b")

impl mul(u16)
mul(a, b) = llvm!("%out", "%out = mul i16 %a, %b")

impl mul(i16)
mul(a, b) = llvm!("%out", "%out = mul i16 %a, %b")

impl mul(u32)
mul(a, b) = llvm!("%out", "%out = mul i32 %a, %b")

impl mul(i32)
mul(a, b) = llvm!("%out", "%out = mul i32 %a, %b")

impl mul(u64)
mul(a, b) = llvm!("%out", "%out = mul i64 %a, %b")

impl mul(i64)
mul(a, b) = llvm!("%out", "%out = mul i64 %a, %b")

// Div
typefn div(a) = (a, a) -> a

impl div(u8)
div(a, b) = llvm!("%out", "%out = sdiv i8 %a, %b")

impl div(i8)
div(a, b) = llvm!("%out", "%out = sdiv i8 %a, %b")

impl div(u16)
div(a, b) = llvm!("%out", "%out = sdiv i16 %a, %b")

impl div(i16)
div(a, b) = llvm!("%out", "%out = sdiv i16 %a, %b")

impl div(u32)
div(a, b) = llvm!("%out", "%out = sdiv i32 %a, %b")

impl div(i32)
div(a, b) = llvm!("%out", "%out = sdiv i32 %a, %b")

impl div(u64)
div(a, b) = llvm!("%out", "%out = sdiv i64 %a, %b")

impl div(i64)
div(a, b) = llvm!("%out", "%out = sdiv i64 %a, %b")

// Mod
typefn mod(a) = (a, a) -> a

impl mod(u8)
mod(a, b) = llvm!("%out", "%out = srem i8 %a, %b")

impl mod(i8)
mod(a, b) = llvm!("%out", "%out = srem i8 %a, %b")

impl mod(u16)
mod(a, b) = llvm!("%out", "%out = srem i16 %a, %b")

impl mod(i16)
mod(a, b) = llvm!("%out", "%out = srem i16 %a, %b")

impl mod(u32)
mod(a, b) = llvm!("%out", "%out = srem i32 %a, %b")

impl mod(i32)
mod(a, b) = llvm!("%out", "%out = srem i32 %a, %b")

impl mod(u64)
mod(a, b) = llvm!("%out", "%out = srem i64 %a, %b")

impl mod(i64)
mod(a, b) = llvm!("%out", "%out = srem i64 %a, %b")


typefn eq(a) = (a, a) -> bool

type neq<a>: (a, a) -> bool
neq(a, b) = !eq(a, b)

impl eq(u8)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i8 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl eq(i8)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i8 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl eq(u16)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i16 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl eq(i16)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i16 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl eq(u32)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i32 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl eq(i32)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i32 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl eq(u64)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i64 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl eq(i64)
eq(a, b) = llvm!(
	"%out","
	%cmp = icmp eq i64 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl eq(char)
eq(Char(a), Char(b)) = a==b

impl eq<a>([a])
eq([], []) = True
eq(a::as, b::bs) = a==b && as==bs
eq(_, _) = False

typefn geq(a) = (a, a) -> bool

impl geq(i8)
geq(a, b) = llvm!(
	"%out", "
	%cmp = icmp sge i8 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl geq(u8)
geq(a, b) = llvm!(
	"%out", "
	%cmp = icmp uge i8 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl geq(i16)
geq(a, b) = llvm!(
	"%out", "
	%cmp = icmp sge i16 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl geq(u16)
geq(a, b) = llvm!(
	"%out", "
	%cmp = icmp uge i16 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl geq(i32)
geq(a, b) = llvm!(
	"%out", "
	%cmp = icmp sge i32 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl geq(u32)
geq(a, b) = llvm!(
	"%out", "
	%cmp = icmp uge i32 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl geq(i64)
geq(a, b) = llvm!(
	"%out", "
	%cmp = icmp sge i64 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl geq(u64)
geq(a, b) = llvm!(
	"%out", "
	%cmp = icmp uge i64 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

typefn leq(a) = (a, a) -> bool

impl leq(i8)
leq(a, b) = llvm!(
	"%out", "
	%cmp = icmp sle i8 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl leq(u8)
leq(a, b) = llvm!(
	"%out", "
	%cmp = icmp ule i8 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl leq(i16)
leq(a, b) = llvm!(
	"%out", "
	%cmp = icmp sle i16 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl leq(u16)
leq(a, b) = llvm!(
	"%out", "
	%cmp = icmp ule i16 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl leq(i32)
leq(a, b) = llvm!(
	"%out", "
	%cmp = icmp sle i32 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl leq(u32)
leq(a, b) = llvm!(
	"%out", "
	%cmp = icmp ule i32 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl leq(i64)
leq(a, b) = llvm!(
	"%out", "
	%cmp = icmp sle i64 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")

impl leq(u64)
leq(a, b) = llvm!(
	"%out", "
	%cmp = icmp ule i64 %a, %b
	%cast = zext i1 %cmp to i8
	%out = insertvalue %bool undef, i8 %cast, 0")
