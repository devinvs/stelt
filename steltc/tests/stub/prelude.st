pub type char = Char(u32)

# pub alias type string = [char]

# maybe is for a result that is something or nothing.
# it will eventually have some special optimizations, specifically
# a maybe<ptr> will use NULL for the None case (saving the 8 bit tag)
pub type maybe<a> = None | Some(a)

# A recursive linked list, in all its glory
pub type list<a> = Nil | Cons(a, list<a>)

# A lookup table
pub type map<a, b> = Map([(a, b)])

# pub lookup: eq('a) => (map<'a, 'b>, 'a) -> maybe<'b>
# lookup(map.Map([]), _) = maybe.None
# lookup(map.Map((a, b)::rest), x) =
	# if a==x
		# then maybe.Some(b)
		# else lookup(rest, x)

# pub not: bool -> bool
# not(x) = llvm!("%out", "%out = select i1 %x, i1 0, i1 1")

#
# Here lies the math spam. This is what I get for having so many int types
#

# maybe macros will fix this eventually, sigh

# Neg
pub typefn neg(a) = a -> a

impl neg(i8)
neg(a) = llvm!("%out", "%out = mul i8 %arg.0, -1")

impl neg(i16)
neg(a) = llvm!("%out", "%out = mul i16 %arg.0, -1")

impl neg(i32)
neg(a) = llvm!("%out", "%out = mul i32 %arg.0, -1")

impl neg(i64)
neg(a) = llvm!("%out", "%out = mul i64 %arg.0, -1")

# Add
pub typefn add(a) = (a, a) -> a

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

# Sub
pub typefn sub(a) = (a, a) -> a

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

# Mul
pub typefn mul(a) = (a, a) -> a

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

# Div
pub typefn div(a) = (a, a) -> a

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

# Mod
pub typefn mod(a) = (a, a) -> a

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


pub typefn eq(a) = (a, a) -> bool

# neq: eq('a) => ('a, 'a) -> bool
# neq(a, b) = !eq(a, b)

impl eq(str)
eq(a, b) = llvm!("%out", "
	%cmp = call i32 @strcmp(ptr %a, ptr %b)
	%out = icmp eq i32 %cmp, 0
")

impl eq(u8)
eq(a, b) = llvm!("%out","%out = icmp eq i8 %a, %b")

impl eq(i8)
eq(a, b) = llvm!("%out","%out = icmp eq i8 %a, %b")

impl eq(u16)
eq(a, b) = llvm!("%out","%out = icmp eq i16 %a, %b")

impl eq(i16)
eq(a, b) = llvm!("%out","%out = icmp eq i16 %a, %b")

impl eq(u32)
eq(a, b) = llvm!("%out","%out = icmp eq i32 %a, %b")

impl eq(i32)
eq(a, b) = llvm!("%out","%out = icmp eq i32 %a, %b")

impl eq(u64)
eq(a, b) = llvm!("%out","%out = icmp eq i64 %a, %b")

impl eq(i64)
eq(a, b) = llvm!("%out","%out = icmp eq i64 %a, %b")

# impl eq([a])
# eq([], []) = True
# eq(a::as, b::bs) = a==b && as==bs
# eq(_, _) = False

pub typefn geq(a) = (a, a) -> bool

impl geq(i8)
geq(a, b) = llvm!("%out", "%out = icmp sge i8 %a, %b")

impl geq(u8)
geq(a, b) = llvm!("%out", "%out = icmp uge i8 %a, %b")

impl geq(i16)
geq(a, b) = llvm!("%out", "%out = icmp sge i16 %a, %b")

impl geq(u16)
geq(a, b) = llvm!("%out", "%out = icmp uge i16 %a, %b")

impl geq(i32)
geq(a, b) = llvm!("%out", "%out = icmp sge i32 %a, %b")

impl geq(u32)
geq(a, b) = llvm!("%out", "%out = icmp uge i32 %a, %b")

impl geq(i64)
geq(a, b) = llvm!("%out", "%out = icmp sge i64 %a, %b")

impl geq(u64)
geq(a, b) = llvm!("%out", "%out = icmp uge i64 %a, %b")

pub typefn leq(a) = (a, a) -> bool

impl leq(i8)
leq(a, b) = llvm!("%out", "%out = icmp sle i8 %a, %b")

impl leq(u8)
leq(a, b) = llvm!("%out", "%out = icmp ule i8 %a, %b")

impl leq(i16)
leq(a, b) = llvm!("%out", "%out = icmp sle i16 %a, %b")

impl leq(u16)
leq(a, b) = llvm!("%out", "%out = icmp ule i16 %a, %b")

impl leq(i32)
leq(a, b) = llvm!("%out", "%out = icmp sle i32 %a, %b")

impl leq(u32)
leq(a, b) = llvm!("%out", "%out = icmp ule i32 %a, %b")

impl leq(i64)
leq(a, b) = llvm!("%out", "%out = icmp sle i64 %a, %b")

impl leq(u64)
leq(a, b) = llvm!("%out", "%out = icmp ule i64 %a, %b")

# pub typefn lt(a) = (a, a) -> bool
