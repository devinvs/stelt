from prelude import add

# Peano Construction
type nat = Zero | Succ(nat)

# 0 + y == y
# x + 0 == x
# (1+x) + y == 1+(x+y)
add : (nat, nat) -> nat
add(nat.Zero, y) = y
add(x, nat.Zero) = x
add(nat.Succ(x), y) = nat.Succ(x + y)

# 0 * y == 0
# x * 0 == 0
# 1 * y == y
# x * 1 == x
# (1+x)*y == y+x*y
mul: (nat, nat) -> nat
mul(nat.Zero, _) = nat.Zero()
mul(_, nat.Zero) = nat.Zero()
mul(nat.Succ(nat.Zero), y) = y
mul(x, nat.Succ(nat.Zero)) = x
mul(nat.Succ(x), y) = y + x*y

from_num: u32 -> nat
from_num(0) = nat.Zero
from_num(x) = nat.Succ(from_num(x-1))

to_num: nat -> nat
to_num(nat.Zero) = 0
to_num(nat.Succ(x)) = 1 + to_num(x)

main: () -> ()
main() = {
	assert add(from_num(12), from_num(7)) == to_num(12+7)
	assert mul(from_num(12), from_num(7)) == to_num(12*7)
}
