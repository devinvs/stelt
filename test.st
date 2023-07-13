type Maybe<a> = None | Some(a)

type unwrap<a>: Maybe<a> -> a
unwrap(Some(a)) = a

