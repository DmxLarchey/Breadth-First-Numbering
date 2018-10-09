#!/bin/sh

make benchmarks.vo

# increase the stack size
export OCAMLRUNPARAM=l=9000000

ocaml try_random_log.ml | tee trl_3q_gc.txt
# then gnuplot with 'plot [t=:] [0:] "trl_3q_gc.txt" using (log($2)/log(2)):3'
