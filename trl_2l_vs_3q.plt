set terminal pdf
set output "trl_2l_vs_3q.pdf"
set title "Two lists versus three lazy lists (with different time scales)"
set xlabel "size"
set ylabel "time"
plot [t=:] [0:] "trl_2l_gc_10_16_600000.txt" using (log($2)/log(2)):(5*$3) smooth unique w l, "trl_3q_gc_10_16_600000.txt" using (log($2)/log(2)):3 smooth unique w l