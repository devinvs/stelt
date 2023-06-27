extern type puts: str -> ()

type Maybe<a> = None | Some(a)

type unwrap<a>: Maybe<a> -> a
unwrap(Maybe.Some(a)) = a

type main: () -> ()

main() = {
    puts(unwrap(Maybe.Some("there might be something here...")))
}
