#!/bin/sh

make benchmarks.vo

# increase the stack size
export OCAMLRUNPARAM=l=900000000,o=1000000

# results without forced major collections before both benchmarks
# with o=80 103 major collections
#       160  59
#       500  17
#      5000   3
#     10000   2
#    100000   1
#   1000000   0

# results with forced major collections before both benchmarks
# with o=10000   8 major collections
#       100000   5
#      1000000   4
#     10000000   4


echo '#use "bench.ml";;' | ocaml

