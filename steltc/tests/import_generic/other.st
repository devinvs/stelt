pub func : [u32] -> u32
func([]) = 0
func(x::xs) = 1 + func(xs)
