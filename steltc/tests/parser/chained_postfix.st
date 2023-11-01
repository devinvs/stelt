type Vec3 = { x u64, y u64, z u64 }
type Cont = { a Vec3 }

type sum: Cont -> u64
sum(c) = c.a.x
