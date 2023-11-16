typefn eq(a) = (a, a) -> bool

type neq: eq(a) => (a, a) -> bool
neq(a, b) =  !(a == b)

// Each of these is specified individually to allow
// for better compiler optimization. If performance is
// unimportant you may define one of these and then
// use it with eq to implement the others
typefn lt(a) = (a, a) -> bool
typefn leq(a) = (a, a) -> bool
typefn gt(a) = (a, a) -> bool
typefn geq(a) = (a, a) -> bool

class Ord(a) = eq(a) + lt(a) + leq(a) + gt(a) + geq(a)
