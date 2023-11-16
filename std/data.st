// The typefunctions that allow us to operate on container types
typefn new(outer) = () -> outer<a>
typefn map(outer) = (outer<a>, a->b) -> outer<b>
typefn flatten(outer) = outer<outer<a>> -> outer<a>
typefn flatmap(outer) = (outer<a>, a->outer<b>) -> outer<a>

//
// Maybe
//

type maybe<a> = None | Some(a)

impl map(maybe)
map(None, _) = None
map(Some(x), f) = Some(f(x))

impl flatten(maybe)
flatten(None) = None
flatten(Some(x)) = x

impl flatmap(maybe)
flatmap(None, _) = None
flatmap(Some(x), f) = f(x)

//
// Slice
//
// similar to vec in rust, represents a contiguous
// section in memory. Represented by a pointer,
// a length, and a capacity.
//
// Holding the capacity has some tradeoffs. It increases
// the size of the slice structure, but it allows for
// much more efficient memory allocation when adding
// single items to the slice.
//
// Same deal with storing an offset. Doing so allows
// for easy fast iteration, but it adds another field

owned type slice<a> = Slice(ptr<a>, u64, u64, u64)

// In order to make creating an empty slice efficient we don't
// allocate here, and instead wait until realloc to get a real
// section of memory.
//
// Since we always bounds check this should work since our
// length/capacity are 0
impl new(slice)
new() = Slice(unsafe ptr(0), 0, 0, 0)

type with_capacity : u64 -> slice<a>
with_capacity(n) = Slice(malloc(n), 0, n, 0)

// Add a single item to the slice.
// Corresponds to the :: operator
type push : (slice<a>, a) -> slice<a>
push(Slice(ptr, len, cap, off), item) =
	if len+off >= cap then
		let new_size =
			if cap == 0 then 10
			else cap * 2 + 1
		in
			let ptr = realloc(ptr, new_size) in
			let ptr = unsafe memset(ptr, off+len, item) in
			Slice(ptr, len+1, new_size, off)
	else
		let ptr = unsafe memset(ptr, off+len, item) in
		Slice(ptr, len+1, cap, off)

// Return the head and tail of the slice, or None if no items left
type pop : slice<a> -> maybe<(a, slice<a>)>
pop(Slice(ptr, len, cap, off)) =
	if off == len then
		None
	else
		let head = unsafe memread(ptr, off) in
		(head, Slice(ptr, len-1, cap, off+1))


// We can't return references, so it is unsafe to
// get an item out of a slice. However, we can
// map on an index and return the result of map
// provided the mapping value takes the value
// in as a reference
type map_index : (&slice<a>, u64, &a -> b) -> maybe<b>
map_index(Slice(ptr, len, cap), i, f) =
	if i >= len then
		None
	else
		Some(f(unsafe memread(ptr, i)))

// We can however do a regular index operation
// if our item type implements copy
type get : copy(a) => (&slice<a>, u64) -> maybe<a>
get(slice, i) = map_index(slice, i, copy)


// Now for some classic container operations

// Since this map takes owernship of the slice
// we are free to overwrite its own buffer if
// the size of the new items is <= the size of
// the current items. I haven't figured out how
// to do this check yet, but it may happen in
// the future
impl map(slice)
map(Slice(ptr, len, cap), f) =
	let old_size = ptr.item_size() in
	// Get the size of the new type
	// this works because the type is inferred
	// in the then clause of the if statement
	let new_ptr = unsafe transmute(ptr) in
	let new_size = new_ptr.item_size() in

	if new_size <= old_size then
		let ptr = unsafe mutate_map(new_ptr, f, len) in
		Slice(ptr, len, cap)
	else
		// If we can't mutate we do a basic copying map
		let ptr = transmute(new_ptr) in
		copy_map(Slice(ptr, len, cap))

type copy_map : (slice<a>, a->b) -> slice<b>
copy_map([], _) = []
copy_map(x::xs, f) = f(x)::copy_map(xs, f)

unsafe type mutate_map : (ptr<b>, a->b, u64) -> ptr<b>
mutate_map(ptr, _, 0) = ptr
mutate_map(ptr, f, n) =
	let aptr = transmute(rest) in
	let a = memread(aptr, n-1) in
	let bptr = transmute(aptr) in
	memwrite(bptr, n-1, f(a))
where rest = mutate_map(ptr, f, n-1)


impl flatten(slice)
flatten(s) =
	// We need to allocate a new buffer to hold all the items
	let size = &s.map(s -> s.len()).sum() in
	let buf = malloc(size) in
	slice_flatten_copy(s, buf)

type slice_copy_all : (slice<slice<a>>, ptr<a>, u64) -> ptr<a>
slice_copy_all([], ptr, _) = ptr
slice_copy_all(Slice(sptr, len, _, soff)::tail, ptr, off) =
	slice_copy_all(tail, memcopy(sptr, soff, ptr, off, len), off+len)

impl flatmap(slice)
flatmap(s, f) = s.map(f).flatten()

//
// Linked List
//

type linked_list<a> = Nil | Cons(a, list<a>)

// :: is only for slices so this is becomes painful
// without the alias
alias type ll = linked_list

impl concat(ll)
concat(ll.Nil, ys) = ys
concat(xs, ll.Nil) = xs
concat(ll.Cons(x, xs), ys) = ll.Cons(x, xs ++ ys)

impl map(ll)
map(ll.Nil, _) = ll.Nil
map(ll.Cons(x, xs), f) = ll.Cons(f(x), map(xs, f))

impl flatten(ll)
flatten(ll.Nil) = ll.Nil
flatten(ll.Cons(x, xs)) = x ++ flatten(xs)

impl flatmap(ll)
flatmap(xs, f) = xs.map(f).flatten()

impl fold(ll)
fold(ll.Nil, _, agg) = agg
fold(ll.Cons(x, xs), f, agg) = fold(xs, f, f(x, agg))

