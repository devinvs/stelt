#!/bin/bash
cargo run -- main.st
opt -O3 main.ll -o main.bc
llc --relocation-model=pic -filetype=obj -O3 main.bc
clang main.o -o out
