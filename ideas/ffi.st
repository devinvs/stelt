// extern functions are defined with the extern type
extern type puts: str -> ()

// In general all calls to outside functions are unsafe

// For owned pointers use box<>, for non-owned use ptr<>
// likewise buffer<> vs slice<>
// ptr and slice should probably only be available as ffi types,
// not constructable outside of a unsafe context.
// yeah I'm thinking we need unsafe functions and sections

unsafe type f: ...

f() = unsafe { ... }

// I'm thinking about a separate stack... not sure I love it