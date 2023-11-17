// an io action
pub type io<'a> = IO(() -> 'a)

// construct a new empty io instance
// useful for telling the compiler about side effects
// that may occur from an external ffi function
pub empty_io : 'a -> io<() -> 'a>
empty_io() = IO(() -> ())

// Mapping a function to an IO action is conceptually
// mapping against the result of the action
impl map(io<'a>)
map(IO(f), g) = IO(_ -> f(g()))

impl flatten(io<'a>)
flatten(IO(IO(f))) = f

// Flatmapping a function to an IO action is conceptually
// composing two IO actions together
impl flatmap(io<'a>)
flatmap(me, f) = me.map(f).flatten()


// At the core of every read/write operation is reading
// and writing slices of bytes.
pub typefn read_bytes(a) = (a, u32) -> io<result<[u8], io_error>>
pub typefn write_bytes(a) = (a, [u8]) -> io<result<(), io_error>>

// Utility methods for reading/writing any data that implements
// to/from bytes
pub read: read_bytes(a) + from_bytes(b) => a -> io<result<maybe<b>, io_error>>
read(f) = read_bytes(f, size)
	.map(res -> res.map(from_bytes))
where size = sizeof(f)

pub write: write_bytes(a) + to_bytes(b) => (a, b) -> io<result<(), io_error>>
write(f, out) = write_bytes(f, out.to_bytes())


