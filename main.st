import test

extern type puts: str -> ()

type main: () -> ()

main() = {
    test.square(5)
    puts("Hello World")
}


