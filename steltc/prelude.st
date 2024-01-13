pub typefn add(a) = (a, a) -> a
pub typefn zero(a) = () -> a
pub typefn eq(a) = (a, a) -> bool

pub type char = Char(u32)
pub type list<a> = Nil | Cons(a, list<a>)

impl add(u32)
// add(x, y) = unsafe llvm!("%out", "%out = add i32 %x, %y")
add(x, y) = 0

impl eq(u32)
// eq(x, y) = unsafe llvm!("%out", "%out = icmp eq i32 %x, %y")
eq(x, y) = False
