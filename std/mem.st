// A raw owned ptr.
//    Dropping is a no-op, this could be a ptr to the stack, heap,
//    or any valid address.
// 
// Invariants:
//   - addr always contain a valid item of type 'a
//   - 'a is never changed by anything that doesn't own this ptr
//
// For a pointer to resource that we don't control, see volatile_ptr
// For a managed pointer on the heap, see box
pub owned type ptr<'a> = pub unsafe Ptr(non_zero<u64>)

// Read an 'a from a ptr with offset
pub unsafe memread : (&ptr<'a>, u64) -> 'a

// Write an 'a to a ptr with offset
pub unsafe memwrite : (ptr<'a>, u64, 'a) -> ptr<'a>

// Copy len bytes from sptr with soff to dptr with doff
pub unsafe memcopy : (ptr<'a>, u64, ptr<'a>, u64, u64)


// A owned ptr to the heap
//   Dropping frees using its allocator
//
// Invariants:
//   - ptr must be on the heap
pub owned type box<'a, 'alloc> = pub unsafe Box(ptr<'a>)

// allocate a new buffer containing an item of type 'a
pub new_box : alloc('alloc, 'a) => 'a -> buf<'a, 'alloc>
new_box(item) =
	// Safety:
	//  - alloc -> we initialize all of the memory
	//  - memwrite -> we are not overwriting our buffer
	//  - Box -> alloc is always on the heap
	let ptr = unsafe memwrite(unsafe alloc(1), 0, item) in
	unsafe Box(ptr)

impl drop(free('alloc) => box<'a, 'alloc>)
// Safety:
//   - Box(ptr) is guaranteed to be on the heap
drop(unsafe Box(ptr)) = unsafe free(ptr)

