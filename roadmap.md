Things that need to be done for this to be a real language (now in a very specific order):

- get lisp program compiling and running
- dynamic/static linking, optimizations, etc as options for cli
- implement string pattern matching (strcmp or memcmp or smthn or idk)
- test type aliases (broken? idk yet)
- add very simple reference counting
  + add tests with valgrind
- test type constraints
  + across modules
  + nested/generic types
- exhaustiveness checking
- caching compilation checks

Future no promises:

Compiler:
- arrays
- vectors w/ simd
- possibly const generics for the above
- string/int type inference
  + string can be array or list or maybe rope?
- unsafe
- testing...

Stdlib:
- list operations
- io
- unicode
  + chars()
  + graphemes()
  + sigh...
- datastructures
  + packed lists
  + maybe some sort of tree
  + sets and maps
- llvm intrinsics
- ffi crap
  + pointers
  + transmute

Tooling:
- package manager/format
  + includes build planner per project
- ide support
  + vscode
  + neovim
  + helix
