extern puts: str -> u32

test: ['a] -> u32
test([]) = puts("true")
# test(False) = puts("false")

main: () -> u32
main() = test([])
