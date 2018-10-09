set terminal pdf
set output "trl_2l_vs_triv.pdf"
set title "Two lists versus trivial implementation - with different sizes"
set xlabel "size"
set ylabel "time"
plot [t=:] [-4:] "trl_2l_gc_10_16_600000.txt" using (log($2)/log(2)):(log($3)/log(2)) smooth unique w l, "trl_triv_gc_10_16_6000.txt" using (log($2)/log(2)):(log($3)/log(2)) smooth unique w l