# stelt

Yet Another Programming Language

<hr>

### Some Specifics

- Static strong typing
  + Local type inference
- Functional, ie immutable w/ first class functions and closures
- Sum and Product types
- Powerful pattern matching
- C-interop
- Opt-in linear typing (todo)
  + allows for mutation
- typefunctions
  + basically typeclasses but easier
+ Fast reference counting by default (todo)
  - via Biased reference counting
+ llvm backend
+ A program that compiles should **never** crash (probably todo lol)
  - outside of ffi of course
+ rust-like unsafe (todo)

Anti-features
+ currying by default
+ macros
+ hidden control flow
+ using the M word

Things I'm thinking about:
+ zig-like async
+ compile time definitions
+ no partial functions in std
  - makes math hard (why division why?)
    + default to 0 for special operator like pony?
      - we will see

### performance < usability < safety

The general guiding principle is to encourage developers to
1. make it work
2. make it right
3. make it fast

So in general we provide defaults that guarantee ease of use and saftey, but at the cost
of performance.

For performance critical sections the developer can strip out the default behavior and replace
it with faster code where needed.
