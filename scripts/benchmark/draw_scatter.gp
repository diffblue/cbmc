# Usage: "gnuplot draw_scatter.gp"

set datafile separator ";"
set terminal png size 1024,1024
set output 'perf_out.png'
set xrange [30:60000]
set yrange [30:60000]
set logscale x 10
set logscale y 10
set ylabel 'time (sec.) on branch'
set xlabel 'time (sec.) on develop'

plot '< join benchmark1.csv benchmark2.csv' using 6:3 with points, \
  x with lines
