set datafile separator ":"
set term png
set output outputfile
set logscale y 10
set yrange  [0.01:100]

plot file using 3 with lines
