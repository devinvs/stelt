pub func : [u32] -> u32
func([]) = 1
func(x::xs) = 1 + func(xs)
