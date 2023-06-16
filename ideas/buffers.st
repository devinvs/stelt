type Bufffer<T> = { addr u64 }

type mset<T> : (own Buffer<T>, u64, T) -> Buffer<T>
type mget<T> : (Buffer<T>, u64) -> T

let b = Buffer(0xbaadf00d)
let b = b.mset(0, 5)

