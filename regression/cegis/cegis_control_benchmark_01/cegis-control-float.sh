#!/bin/bash
export PATH=${PATH//cbmc-5190/cbmc-trunk-diffblue-control-synthesis}
export PATH=${PATH}:/users/pkesseli/software/cpp/cbmc/cbmc-trunk-diffblue-control-synthesis/src/cegis:/users/pkesseli/software/cpp/cbmc/cbmc-trunk-diffblue-control-synthesis-analyzer/src/goto-analyzer

benchmark_basedir='/users/pkesseli/software/cpp/cbmc/cbmc-trunk-diffblue-control-synthesis/regression'
cd ${benchmark_basedir}

benchmark_dir=$1
cd ${benchmark_dir}

function get_exponent_width() {
  if [ $1 -le 8 ]; then return 2; fi
  if [ $1 -le 10 ]; then return 3; fi
  if [ $1 -le 12 ]; then return 4; fi
  if [ $1 -le 14 ]; then return 5; fi
  if [ $1 -le 16 ]; then return 6; fi
  if [ $1 -le 26 ]; then return 7; fi
  if [ $1 -le 37 ]; then return 8; fi
  if [ $1 -le 48 ]; then return 9; fi
  if [ $1 -le 58 ]; then return 10; fi
  return 11
}

for word_width in {8..64}; do
  get_exponent_width ${word_width}
  exponent_width=$?
  fraction_width=$((word_width - exponent_width - 1))
  echo "exp: $exponent_width, frac: $fraction_width"
  cegis -D _EXPONENT_WIDTH=${fraction_width} -D _FRACTION_WIDTH=${exponent_width} --cegis-control --cegis-statistics --cegis-max-size 1 *.c
  if [ $? -eq 0 ]; then exit 0; fi
done
exit 10
