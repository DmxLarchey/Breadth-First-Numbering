#/bin/sh

make benchmarks.vo
echo '#use "bench.ml";;' | ocaml

