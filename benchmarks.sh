#/bin/sh

make benchmarks.vo

# increase the stack size
export OCAMLRUNPARAM=l=80000000

echo '#use "bench.ml";;' | ocaml

