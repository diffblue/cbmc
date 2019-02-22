# Usage: "gnuplot draw_scatter.gp"

set datafile separator ";"
set terminal png size 1024,1024
set output 'perf_out.png'
set xrange [30:60000]
set yrange [30:60000]
set logscale x 10
set logscale y 10
set xlabel 'time (sec.) on develop'
set ylabel 'time (sec.) on branch'

plot '< join develop.csv branch.csv' using 3:6 with points, \
  x with lines
