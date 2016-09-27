#!/bin/bash
export PATH=${PATH//cbmc-5190/cbmc-trunk-diffblue-control-synthesis}
export PATH=${PATH}:/users/pkesseli/software/cpp/cbmc/cbmc-trunk-diffblue-control-synthesis/src/cegis:/users/pkesseli/software/cpp/cbmc/cbmc-trunk-diffblue-control-synthesis-analyzer/src/goto-analyzer

benchmark_basedir='/users/pkesseli/software/cpp/cbmc/cbmc-trunk-diffblue-control-synthesis/regression'
cd ${benchmark_basedir}

benchmark_dir=$1
cd ${benchmark_dir}

for word_width in {8..64..2}; do
  echo "width: $word_width"
  cegis -D _FIXEDBV -D _CONTROL_FLOAT_WIDTH=${word_width} --fixedbv --cegis-control --cegis-statistics --cegis-max-size 1 *.c >/dev/null 2>&1
  if [ $? -eq 0 ]; then exit 0; fi
done
exit 10
