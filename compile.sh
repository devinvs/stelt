#!/bin/bash
cargo run
llc --relocation-model=pic -filetype=obj -O3 out.ll
clang out.o -o out
