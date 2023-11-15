# steltc

The Stelt Compiler

- [Design](#design)
  + [Error Handling](#error-handling)
  + [Parallelism](#parallelism)
  + [Incrementalism](#incrementalism)
  + [Tokens](#tokens)
  + [Parse Tree](#parse-tree)
  + [AST](#ast)
    - [Modules](#modules)
  + [MIR](#mir)
  + [Type Checking / Type Inference / Constraint Checking](#type-checking--type-inference--constraint-checking)
  + [Monomorphization](#monomorphization)
  + [LIR](#lir)
  + [Codegen](#codegen)

## Design

This section intends to represent the future design goals of the
stelt compiler, not as it stands now. This is intended to be a good
description of each stage and the their intent.

This document is not concerned in the design of the language, only
the implementation of this compiler towards some of its design goals.

### Error Handling

Good errors should be at the core of every stage of the compiler, but
what a good error is depends on context. In an IDE errors should be
concise, one or two lines at most. In a terminal errors should be
longer with more supporting information, though too long will
make dealing with multiple errors overwhelming.

Every error in stelt will include:
- a source location
- a unique error code
- a concise message
- a longer explanation of the underlying principle
- a fix or example of a well-formed program

These attributes can be mixed and matched for each context. Additionally,
an error database could be published with all the necessary context and
more, hopefully indexable by the unique error codes.

Code schema is TBD, but it should ensure good SEO and not conflict with
any other naming scheme.

Error messages should avoid language that is too technical or specific
to the world of compilers. Terms that can't be avoided or are necessary
for good usage of the language should be defined where possible.

Another principle that should guide the design of error messages in the
compiler is that as many errors as we can detect should be returned.
This means that each stage should be able to continue the validation
steps and return a list of errors rather than quitting after the first.
A potential but not certain implementation could involve handling each
function or item independently after parsing, so errors in one function
won't prevent the checking of other functions. This is referred to as
a "dry-run", where the only expected output is more errors.

## Parallelism

The langauge has been designed such that most of the stages of the
compiler can be run in parallel without needing to know anything
about other modules. Every file is one module, and each module can
be compiled almost independently from each other.

There are two places where this breaks down. The first is imports
and typechecking. In order to prove that a module is correct, it
must know the types of the things that it imports. Thus typechecking
depends on the parse tree of another module.

Similarly, the nature of typefunctions and impls are global. It is
unavoidable to treat these as a global resource, though each module
is only responsible for compiling its own impls.

## Incrementalism

I don't know if this is a word. Either way, it gets the meaning across.
Each step in the compiler should be able to be cached in a way that is
useful for incremental compilation. If a module is already compiled and
has not been changed, we don't need to go through the process of parsing
and validating and typechecking and the rest of the pipeline. But, we
do need to know exported names, type information, generic impls, etc.

It is useful also from a code quality standpoint to enforce strong boundaries
between each stage, such that we don't know whether we are acting on a
"live" program or a cached version.

## Tokens

Every token should know what type of token it is, the start of its location
in the source code, and optionally an index into a auxillary array for string
and number constants.

The full source location is from the start to the end, which can be derived
from the token type and the value in the auxillary array.

The lexer is a function from a file string to a list of tokens.
It should return a list of token errors alongside the list of tokens
such that a dry-run of parsing may be possible.

Token lexing should be more flexible than the language allows since token
error messages are inherently limited.

There is a hard balance between identifying unrecoverable errors, such as
mismatched parentheses, and a recoverable error, such as an identifier
with an invalid token. The lexer should do its best to lex as much of
the program as possible while also indicating whether it is prudent to
continue to attempt to parse the program.

The lexer is trivially parallel partitioned by file.

## Parse Tree

The parse tree is not a faithful recreation of the program text. It
will automatically convert syntactic sugar into their equivalent forms.

Each parse tree node doesn't contain a source location, but instead an
index into the token array, from which the source locations can be computed.

When possible the parser should try to recover and continue parsing. Again
this is a delicate balance, and some heuristics may be necessary to know
when it is time to give up.

The parser is trivially parallel partitioned by file.

## AST

The AST is a fully validated parse tree with guaranteed unique names. Every
name should be in its "canonical" form, which is prefixed by its module path.

This is the best place to catch a variety of errors since the source information
has not been distorted by going through intermedate representations. The
downside is that we don't have access to type information at this stage.

There are a couple of transformations (after validation) that will simplify our
work in future stages by not requiring us to modify type information. Ideally
types never change once inferred.

This includes:
- Inserting allocations into recursive types
- Converting functions into closures (a tuple)
- possibly more

This is just based on my terrible experience of trying to run transformations
on the tree after type-checking while preserving type information (which is
necessary for llvm). I sincerely hope this will take away much of the complexity
especially in the lir stage.

### Modules

As part of this resolution step each module will create a module object which is
cacheable and contains all the information that other modules will need for
imports, namely:
- public declared types
- public declared data
- public generic function bodies (for monomorphization)
- public typefunctions
- all impls (impls are always public)

This is the only step that requires synchronization between all parse trees,
so we depend on incremental compilation and caching of the module information
to speed up this step in successive compilations.

All imported module information is included in the AST of each module, so
all future steps can happen in parallel partitioned by module.

## MIR

The mir is intended to be a much simpler tree that is a balance between what
hardware actually does and a well-typed lambda calculus. It is prudent for
higher level analysis such as type-checking, generic constraints, owned types,
and some optimizations.

This is likely the best place to include beta/eta reduction style optimizations.
(also maybe I'll make this ir CPS??? Idk maybe)

## Type Checking / Type Inference / Constraint Checking

These three steps all happen in tandem so we will consider them together.

All top-level expressions must have a declared type, so we consider that
we are checking each expression against its declared type while we are
running inference.

Additionally, we aggregate the necessary generic constraints at each
call to a typefunction which are checked at the end of typechecking
the function against "provided" constraints (which are in the declared
type) and typefunction impls (provided globally).

Typechecking should produce a new mir tree with filled in type information,
but depends on unchanging type definitions and declarations. Thus, if
this immutable data is shared typechecking could be parallelized on a
per function basis. A green-threading approach may be suitable to minimize
the cost of checking small functions.

Functions that pass type-checking may run through future validation stages
in a dry-run fashion if the whole program does not pass typechecking.

## Monomorphization

This is the demarcation between validating stages and compiling stages.
Our primary goal is from now on not to see if a program is correct, but
assume it is and represent it as efficiently as possible.

Monomorphization is responsible for creating unique functions for every
version of a generic function and type that are used. It is also responsible
for resolving typefunctions to their concrete implementations.

This step is fairly complicated, more to be written later. Until then see
the implementation in `src/mir.rs`, with special note to the breadth-first
search through the program tree.

## LIR

The future design of the LIR is very likely to change from the current
implementation in the rust version of the compiler. I'm considering
two different ideas and really don't have any predisposition either way.

One idea is to make an SSA representation. This will mesh nicely with
llvm and a lot of the ideas will transfer well. I hope that this will
simplify the idea of thunks, which currently make code generation too
complex.

The other idea is to go the CPS route. I'm less familiar with this
option, but am aware that it is the way "functional" languages
solve this problem (except notably haskell which is ssa I believe). 
I'm worried that this will result in too much reliance on the heap
and complicate the unboxed by default types. Additionally it may
obfuscate source and type information to an extent that is
unhelpful. **Please note, I don't know what I'm talking about. I'm
still reading and thinking.**

Either way, all types need to be converted to their llvm representations.

Another thing I am considering changing is compiling each type to their
anonymous llvm type and not emit any named llvm types at all. This will
simplify some aspects but removes some of the safety measures in llvm
and may make debugging/source information less valuable/applicable.

This is still a very big TBD.

## Codegen

I hate llvm. I love llvm. It is both amazingly great and empowering but
also very annoying sometimes. One big annoyance is that the "preferred"
way to use it is to link to and use their C++ libraries. This is annoying
to me and is not the way I wrote the first compiler (though I tried at first).

Three options:
- Give up and link to C++. This probably involves the least amount of reinventing
    but it means we have to include llvm as part of the build process for the
    compiler and it increases binary size (if we statically link, which is probably yes).
- Output llvm ir as text. This is easy, and we will need to do it anyways in some form.
    Llvm's library provides this functionality as well. It is less efficient and requires
    reparsing of the ir files.
- Output llvm bytecode. This is complex and reinvents a lot of the wheel, but it is more
    efficient than outputting text.

Options 2 and 3 feel more "unixy" to me, just because we would ship steltc which would
pipe into opt which would pipe into llc. My worry is that these tools are only meant
for testing and not for creating a production compiler pipeline.

Tbh I already know that 1 is likely the best option, I just don't want to admit yet. I'll
come around eventually.

