pub typefn add(a) = (a, a) -> a
pub typefn zero(a) = () -> a
pub typefn eq(a) = (a, a) -> bool

pub type char = Char(u32)
pub type list<a> = Nil | Cons(a, list<a>)

impl add(u32)
add(x, y) = llvm!("%out", "%out = add i32 %x, %y")

impl eq(u32)
eq(x, y) = llvm!("%out", "%out = icmp eq i32 %x, %y")
