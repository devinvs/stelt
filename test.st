extern type puts: str -> ()

type Maybe<a> = None | Some(a)

type print: Maybe<str> -> ()
print(Maybe.None) = puts("None")
print(Maybe.Some(b)) = puts(b)


type main: () -> ()
main() = print(Maybe.None())
