# stelt

brought to you by a year of depression followed by a few better ones

<hr>

### Some Specifics which definitely haven't changed over the course of building this language

- Static strong typing
  + Local type inference
- Functional, ie immutable w/ first class functions and closures
- Sum and Product types
- Powerful pattern matching
- C-interop (hopefully easy but idk about structs and whatnot yet)
- typefunctions
  + basically typeclasses but easier
+ Fast reference counting by default (todo)
  - via Biased reference counting or maybe other fancy techniques
+ llvm backend
  - others in the works possibly
+ go-like concurrency
+ multi-platform/arch i hope

Things I'm thinking about:
+ zig-like async
+ compile time definitions
+ no partial functions in std
  - makes math hard (why division why?)
    + default to 0 for special operator like pony?
      - we will see
        + then again probably not if we are being completely honest.
          programs that are wrong should crash if not caught.
