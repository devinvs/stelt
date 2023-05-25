#!/bin/bash
cargo run
llc --relocation-model=pic -filetype=obj out.ll
clang out.o -o out
