import test

extern type puts: str -> ()

type main: () -> ()
main() = {
    puts(test.unwrap(test.Some("there might be something here...")))
}


