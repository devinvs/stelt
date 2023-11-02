Things that need to be done for this to be a real language (in no particular order):

Compiler:
- imports that make sense
- type aliases
- self hosting compiler
- reference counting gc
- type constraints
- exhaustiveness checking
- opt-in linear types
  + safe functional mutation
  + this messes with generics, will need to ponder
    - maybe have derivable copy?
- better modules (probably not first class)
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
