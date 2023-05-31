#!/bin/bash
cargo run
llc --relocation-model=pic -filetype=obj -O0 out.ll
clang out.o -o out
