#/bin/sh

make benchmarks.vo

# increase the stack size
export OCAMLRUNPARAM=l=8000000

echo '#use "bench.ml";;' | ocaml

