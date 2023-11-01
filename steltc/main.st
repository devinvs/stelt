type list<a> = Nil | Cons(a, list<a>)

type pop<a>: [a] -> [a]
pop([]) = []
pop(x::xs) = xs
