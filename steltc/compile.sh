#!/bin/bash
cargo run -- main.st
opt -O3 build/main.ll -o build/main.bc
opt -O3 build/prelude.ll -o build/prelude.bc
llc --relocation-model=pic -filetype=obj -O3 build/main.bc
llc --relocation-model=pic -filetype=obj -O3 build/prelude.bc
clang build/main.o build/prelude.o -o out
