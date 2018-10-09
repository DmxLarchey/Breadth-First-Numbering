set terminal pdf
set output "trl_impact_of_flambda_3q.pdf"
set title "Impact of flambda option for OCaml for 3q impl."
set xlabel "size"
set ylabel "time"
plot [t=:] [0:] "trl_3q_gc_10_16_600000_flambda.txt" using (log($2)/log(2)):3 smooth unique w l, "trl_3q_gc_10_16_600000.txt" using (log($2)/log(2)):3 smooth unique w l
