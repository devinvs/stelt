from prelude import eq

type a = P | Q

impl eq(a)
eq(a.P, a.P) = True
eq(a.Q, a.Q) = True
eq(_, _) = False

main: () -> bool
main() = a.P() == a.P()
