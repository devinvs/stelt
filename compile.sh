#!/bin/bash
cargo run -- main.st
llc --relocation-model=pic -filetype=obj -O3 main.ll
clang main.o -o out
