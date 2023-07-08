extern type puts: str -> ()

type Maybe<a> = None | Some(a)

type unwrap<a>: Maybe<a> -> a
unwrap(Some(a)) = a

type main: () -> ()

main() = {
    puts(unwrap(Some("there might be something here...")))
}
