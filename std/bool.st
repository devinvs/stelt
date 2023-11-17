pub not: bool -> bool
not(x) = llvm!("%out", "%out = select i1 %x, i1 0, i1 1")

// Most calls to and/or get optimized so that we can
// have some lazy short-circuit optimizations.
// But we can still pass these around as first class
// functions so we need a default implementation
pub and: (bool, bool) -> bool
and(x, y) = llvm!("%out", "%out = and i1 %x, %y")

pub or: (bool, bool) -> bool
or(x, y) = llvm!("%out", "%out = or i1 %x, %y")

