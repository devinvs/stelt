from a import b, test

typefn eq(a) = (a, a) -> a

type freul: test -> bool
freul(test.P) = True
freul(test.Q) = False

type main: () -> bool
main() = b()
