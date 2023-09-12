typefn next(iter, a) = iter -> (a, iter)

// in this example nats is an ascending iterator over natural numbers
type nats = Nats(u32)

impl next(nats, usize)
next(Nats(n)) = (n, Nats(n+1))

// now we can define an iterator over a range from [n..m)
type range = Range(i32, i32, i32)    // n, m, skip

// return maybe because the iterator will end
impl next(range, maybe<usize>)
next(Range(n, m, skip)) =
    if n>=m then
        // If n==m then we have exhausted the range
        (None, Range(n, m, skip))
    else
        (Some(n), Range(n+skip, m, skip))

// I bet we can define a list as an iterator too
// ...well kinda, need way to add type vars to impl
impl next<a>(list<a>, maybe<a>)
next([]) = (None, [])
next(x::xs) = (Some(x), xs)

// so lets saw we initialize an iterator from 5 to 8
// let r = Range(5, 8) in
// let (a, r) = r.next() in
// let (b, r) = r.next() in
// let (c, r) = r.next() in
// a + b + c


