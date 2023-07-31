type Bool = False | True
type Maybe<a> = None | Some(a)
type List<a> = Nil | Cons(a, List<a>)

type llvm!<a> : (str, str) -> a
