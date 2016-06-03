#!/bin/bash
test_cases=`find cbmc-java/datastax/ -name *.desc -exec dirname {} \;`
./test.pl -c $1 ${test_cases}

count=0
for test_case in ${test_cases}; do
  out_file=`find ${test_case} -name '*.out'`
  if grep -q "identifier.*not found" ${out_file}; then
    echo ${out_file}
    count=$((${count}+1))
  fi
done;
echo "Missing symbols: ${count}"
