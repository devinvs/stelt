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

zero: nat
zero = nat.Zero()

one: nat
one = nat.Succ(nat.Zero())

two: nat
two = nat.Succ(nat.Succ(nat.Zero()))

three: nat
three = nat.Succ(nat.Succ(nat.Succ(nat.Zero())))

four: nat
four = nat.Succ(nat.Succ(nat.Succ(nat.Succ(nat.Zero()))))

main: () -> ()
main() = {
	assert two == one+one
	assert one == one+zero
	assert three == one+two
	assert four == two*two
	assert two*two*two == four+four
}
