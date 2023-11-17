pub typefn eq(a) = (a, a) -> bool

pub neq: eq(a) => (a, a) -> bool
neq(a, b) =  !(a == b)

// Each of these is specified individually to allow
// for better compiler optimization. If performance is
// unimportant you may define one of these and then
// use it with eq to implement the others
pub typefn lt(a) = (a, a) -> bool
pub typefn leq(a) = (a, a) -> bool
pub typefn gt(a) = (a, a) -> bool
pub typefn geq(a) = (a, a) -> bool

class Ord(a) = eq(a) + lt(a) + leq(a) + gt(a) + geq(a)
