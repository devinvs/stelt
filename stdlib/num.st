from std.data import maybe
from std.cmp import Ord

// A non_zero number.
//
// Used to ensure that division operators are total.
// Also allows for layout optimization of maybe types
// where a implements zero()
pub type non_zero<a> = NonZero(a)

pub non_zero: zero(a) => a -> non_zero<a>
non_zero(x) = if x == 0 then None else Some(NonZero(x))

impl add(add(a) => non_zero<a>)
add(NonZero(x), NonZero(y)) = NonZero(x+y)

impl mul(mul(a) => non_zero<a>)
mul(NonZero(x), NonZero(y)) = NonZero(x*y)


// typefunctions for basic mathematical operations
pub typefn zero(a) = a
pub typefn add(a) = (a, a) -> a
pub typefn sub(a) = (a, a) -> a
pub typefn mul(a) = (a, a) -> a
pub typefn neg(a) = a -> a

// In order to keep these functions total they
// take a non_zero for their second parameter.
pub typefn div(a) = (a, non_zero<a>) -> a
pub typefn mod(a) = (a, non_zero<a>) -> a
pub typefn rem(a) = (a, non_zero<a>) -> a
 
// Useful typeclasses for dealing with numbers

class Ring(a) = add(a) + mul(a)
class Nat(a) = Ring(a) + zero(a) + sub(a) + div(a) + mod(a) + Ord(a)
class Int(a) = Nat(a) + neg(a)

// And then the bit operations...
pub typefn bit_not(a) = a -> a	// b~
pub typefn bit_and(a) = a -> a	// b&
pub typefn bit_or(a) = a -> a	// b|
pub typefn bit_xor(a) = a -> a	// b^

class Bits(a) = bit_not(a) + bit_and(a) + bit_or(a) + bit_xor(a)

// Lets implement all the relevant typefn for all the numbers.
// I'm so glad my language doesn't have macros!!!


// u8
impl zero(u8)
zero = 0

impl add(u8)
add(a, b) = llvm!("%out", "%out = add i8 %a, %b")

impl sub(u8)
sub(a, b) = llvm!("%out", "%out = sub i8 %a, %b")

impl mul(u8)
mul(a, b) = llvm!("%out", "%out = mul i8 %a, %b")

impl div(u8)
div(x, y) = llvm!("%out", "%out = div i8 %x, %y")

impl mod(u8)
mod(x, y) = llvm!("%out", "%out = mod i8 %x, %y")

impl eq(u8)
eq(x, y) = llvm!("%out", "%out = icmp eq i8 %x, %y")

impl lt(u8)
lt(x, y) = llvm!("%out", "%out = icmp ult i8 %x, %y")

impl leq(u8)
leq(x, y) = llvm!("%out", "%out = icmp sle i8 %x, %y")

impl gt(u8)
leq(x, y) = llvm!("%out", "%out = icmp ugt i8 %x, %y")

impl geq(u8)
leq(x, y) = llvm!("%out", "%out = icmp uge i8 %x, %y")

impl bit_not(u8)
bit_not(x) = llvm!("%out", "%out = xor i8 %x, -1")

impl bit_or(u8)
bit_or(x, y) = llvm!("%out", "%out = or i8 %x, %y")

impl bit_and(u8)
bit_and(x, y) = llvm!("%out", "%out = and i8 %x, %y")

impl bit_xor(u8)
bit_xor(x, y) = llvm!("%out", "%out = xor i8 %x, %y")


// i8
impl zero(i8)
zero = 0

impl neg(i8)
neg(x) = llvm!("%out", "%out = mul i8 %x, -1")

impl add(i8)
add(a, b) = llvm!("%out", "%out = add i8 %a, %b")

impl sub(i8)
sub(a, b) = llvm!("%out", "%out = sub i8 %a, %b")

impl mul(i8)
mul(a, b) = llvm!("%out", "%out = mul i8 %a, %b")

impl div(i8)
div(x, y) = llvm!("%out", "%out = div i8 %x, %y")

impl mod(i8)
mod(x, y) = llvm!("%out", "%out = mod i8 %x, %y")

impl eq(i8)
eq(x, y) = llvm!("%out", "%out = icmp eq i8 %x, %y")

impl lt(i8)
lt(x, y) = llvm!("%out", "%out = icmp slt i8 %x, %y")

impl leq(i8)
leq(x, y) = llvm!("%out", "%out = icmp sle i8 %x, %y")

impl gt(i8)
leq(x, y) = llvm!("%out", "%out = icmp sgt i8 %x, %y")

impl geq(i8)
leq(x, y) = llvm!("%out", "%out = icmp sge i8 %x, %y")

impl bit_not(i8)
bit_not(x) = llvm!("%out", "%out = xor i8 %x, -1")

impl bit_or(i8)
bit_or(x, y) = llvm!("%out", "%out = or i8 %x, %y")

impl bit_and(i8)
bit_and(x, y) = llvm!("%out", "%out = and i8 %x, %y")

impl bit_xor(i8)
bit_xor(x, y) = llvm!("%out", "%out = xor i8 %x, %y")

// u16
impl zero(u16)
zero = 0

impl add(u16)
add(a, b) = llvm!("%out", "%out = add i16 %a, %b")

impl sub(u16)
sub(a, b) = llvm!("%out", "%out = sub i16 %a, %b")

impl mul(u16)
mul(a, b) = llvm!("%out", "%out = mul i16 %a, %b")

impl div(u16)
div(x, y) = llvm!("%out", "%out = div i16 %x, %y")

impl mod(u16)
mod(x, y) = llvm!("%out", "%out = mod i16 %x, %y")

impl eq(u16)
eq(x, y) = llvm!("%out", "%out = icmp eq i16 %x, %y")

impl lt(u16)
lt(x, y) = llvm!("%out", "%out = icmp ult i16 %x, %y")

impl leq(u16)
leq(x, y) = llvm!("%out", "%out = icmp sle i16 %x, %y")

impl gt(u16)
leq(x, y) = llvm!("%out", "%out = icmp ugt i16 %x, %y")

impl geq(u16)
leq(x, y) = llvm!("%out", "%out = icmp uge i16 %x, %y")

impl bit_not(u16)
bit_not(x) = llvm!("%out", "%out = xor i16 %x, -1")

impl bit_or(u16)
bit_or(x, y) = llvm!("%out", "%out = or i16 %x, %y")

impl bit_and(u16)
bit_and(x, y) = llvm!("%out", "%out = and i16 %x, %y")

impl bit_xor(u16)
bit_xor(x, y) = llvm!("%out", "%out = xor i16 %x, %y")


// i16
impl zero(i16)
zero = 0

impl neg(i16)
neg(x) = llvm!("%out", "%out = mul i16 %x, -1")

impl add(i16)
add(a, b) = llvm!("%out", "%out = add i16 %a, %b")

impl sub(i16)
sub(a, b) = llvm!("%out", "%out = sub i16 %a, %b")

impl mul(i16)
mul(a, b) = llvm!("%out", "%out = mul i16 %a, %b")

impl div(i16)
div(x, y) = llvm!("%out", "%out = div i16 %x, %y")

impl mod(i16)
mod(x, y) = llvm!("%out", "%out = mod i16 %x, %y")

impl eq(i16)
eq(x, y) = llvm!("%out", "%out = icmp eq i16 %x, %y")

impl lt(i16)
lt(x, y) = llvm!("%out", "%out = icmp slt i16 %x, %y")

impl leq(i16)
leq(x, y) = llvm!("%out", "%out = icmp sle i16 %x, %y")

impl gt(i16)
leq(x, y) = llvm!("%out", "%out = icmp sgt i16 %x, %y")

impl geq(i16)
leq(x, y) = llvm!("%out", "%out = icmp sge i16 %x, %y")

impl bit_not(i16)
bit_not(x) = llvm!("%out", "%out = xor i16 %x, -1")

impl bit_or(i16)
bit_or(x, y) = llvm!("%out", "%out = or i16 %x, %y")

impl bit_and(i16)
bit_and(x, y) = llvm!("%out", "%out = and i16 %x, %y")

impl bit_xor(i16)
bit_xor(x, y) = llvm!("%out", "%out = xor i16 %x, %y")

// u32
impl zero(u32)
zero = 0

impl add(u32)
add(a, b) = llvm!("%out", "%out = add i32 %a, %b")

impl sub(u32)
sub(a, b) = llvm!("%out", "%out = sub i32 %a, %b")

impl mul(u32)
mul(a, b) = llvm!("%out", "%out = mul i32 %a, %b")

impl div(u32)
div(x, y) = llvm!("%out", "%out = div i32 %x, %y")

impl mod(u32)
mod(x, y) = llvm!("%out", "%out = mod i32 %x, %y")

impl eq(u32)
eq(x, y) = llvm!("%out", "%out = icmp eq i32 %x, %y")

impl lt(u32)
lt(x, y) = llvm!("%out", "%out = icmp ult i32 %x, %y")

impl leq(u32)
leq(x, y) = llvm!("%out", "%out = icmp sle i32 %x, %y")

impl gt(u32)
leq(x, y) = llvm!("%out", "%out = icmp ugt i32 %x, %y")

impl geq(u32)
leq(x, y) = llvm!("%out", "%out = icmp uge i32 %x, %y")

impl bit_not(u32)
bit_not(x) = llvm!("%out", "%out = xor i32 %x, -1")

impl bit_or(u32)
bit_or(x, y) = llvm!("%out", "%out = or i32 %x, %y")

impl bit_and(u32)
bit_and(x, y) = llvm!("%out", "%out = and i32 %x, %y")

impl bit_xor(u32)
bit_xor(x, y) = llvm!("%out", "%out = xor i32 %x, %y")


// i32
impl zero(i32)
zero = 0

impl neg(i32)
neg(x) = llvm!("%out", "%out = mul i32 %x, -1")

impl add(i32)
add(a, b) = llvm!("%out", "%out = add i32 %a, %b")

impl sub(i32)
sub(a, b) = llvm!("%out", "%out = sub i32 %a, %b")

impl mul(i32)
mul(a, b) = llvm!("%out", "%out = mul i32 %a, %b")

impl div(i32)
div(x, y) = llvm!("%out", "%out = div i32 %x, %y")

impl mod(i32)
mod(x, y) = llvm!("%out", "%out = mod i32 %x, %y")

impl eq(i32)
eq(x, y) = llvm!("%out", "%out = icmp eq i32 %x, %y")

impl lt(i32)
lt(x, y) = llvm!("%out", "%out = icmp slt i32 %x, %y")

impl leq(i32)
leq(x, y) = llvm!("%out", "%out = icmp sle i32 %x, %y")

impl gt(i32)
leq(x, y) = llvm!("%out", "%out = icmp sgt i32 %x, %y")

impl geq(i32)
leq(x, y) = llvm!("%out", "%out = icmp sge i32 %x, %y")

impl bit_not(i32)
bit_not(x) = llvm!("%out", "%out = xor i32 %x, -1")

impl bit_or(i32)
bit_or(x, y) = llvm!("%out", "%out = or i32 %x, %y")

impl bit_and(i32)
bit_and(x, y) = llvm!("%out", "%out = and i32 %x, %y")

impl bit_xor(i32)
bit_xor(x, y) = llvm!("%out", "%out = xor i32 %x, %y")

// u64
impl zero(u64)
zero = 0

impl add(u64)
add(a, b) = llvm!("%out", "%out = add i64 %a, %b")

impl sub(u64)
sub(a, b) = llvm!("%out", "%out = sub i64 %a, %b")

impl mul(u64)
mul(a, b) = llvm!("%out", "%out = mul i64 %a, %b")

impl div(u64)
div(x, y) = llvm!("%out", "%out = div i64 %x, %y")

impl mod(u64)
mod(x, y) = llvm!("%out", "%out = mod i64 %x, %y")

impl eq(u64)
eq(x, y) = llvm!("%out", "%out = icmp eq i64 %x, %y")

impl lt(u64)
lt(x, y) = llvm!("%out", "%out = icmp ult i64 %x, %y")

impl leq(u64)
leq(x, y) = llvm!("%out", "%out = icmp sle i64 %x, %y")

impl gt(u64)
leq(x, y) = llvm!("%out", "%out = icmp ugt i64 %x, %y")

impl geq(u64)
leq(x, y) = llvm!("%out", "%out = icmp uge i64 %x, %y")

impl bit_not(u64)
bit_not(x) = llvm!("%out", "%out = xor i64 %x, -1")

impl bit_or(u64)
bit_or(x, y) = llvm!("%out", "%out = or i64 %x, %y")

impl bit_and(u64)
bit_and(x, y) = llvm!("%out", "%out = and i64 %x, %y")

impl bit_xor(u64)
bit_xor(x, y) = llvm!("%out", "%out = xor i64 %x, %y")


// i64
impl zero(i64)
zero = 0

impl neg(i64)
neg(x) = llvm!("%out", "%out = mul i64 %x, -1")

impl add(i64)
add(a, b) = llvm!("%out", "%out = add i64 %a, %b")

impl sub(i64)
sub(a, b) = llvm!("%out", "%out = sub i64 %a, %b")

impl mul(i64)
mul(a, b) = llvm!("%out", "%out = mul i64 %a, %b")

impl div(i64)
div(x, y) = llvm!("%out", "%out = div i64 %x, %y")

impl mod(i64)
mod(x, y) = llvm!("%out", "%out = mod i64 %x, %y")

impl eq(i64)
eq(x, y) = llvm!("%out", "%out = icmp eq i64 %x, %y")

impl lt(i64)
lt(x, y) = llvm!("%out", "%out = icmp slt i64 %x, %y")

impl leq(i64)
leq(x, y) = llvm!("%out", "%out = icmp sle i64 %x, %y")

impl gt(i64)
leq(x, y) = llvm!("%out", "%out = icmp sgt i64 %x, %y")

impl geq(i64)
leq(x, y) = llvm!("%out", "%out = icmp sge i64 %x, %y")

impl bit_not(i64)
bit_not(x) = llvm!("%out", "%out = xor i64 %x, -1")

impl bit_or(i64)
bit_or(x, y) = llvm!("%out", "%out = or i64 %x, %y")

impl bit_and(i64)
bit_and(x, y) = llvm!("%out", "%out = and i64 %x, %y")

impl bit_xor(i64)
bit_xor(x, y) = llvm!("%out", "%out = xor i64 %x, %y")
