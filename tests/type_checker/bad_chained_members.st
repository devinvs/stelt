type Vec3 = { x u64, y u64, z u64 }
type Cont = { a Vec3 }

type sum: Cont -> i64
sum(c) = c.a.x
