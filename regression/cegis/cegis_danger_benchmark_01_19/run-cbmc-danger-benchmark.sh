#!/bin/bash
tool=$1
export out_file=$2.cbmc.out
rm ${out_file} 2>/dev/null
timeout_time=300

start_time=$(($(date +%s%N)/1000000))
timeout --kill-after=10 ${timeout_time} bash ${tool} --no-unwinding-assertions $2
if [ $? -eq 124 ]; then
  timed_out=0
else
  timed_out=1
fi
end_time=$(($(date +%s%N)/1000000))
duration=$(echo "${end_time} - ${start_time}" | bc)
grep "VERIFICATION FAILED" ${out_file} >/dev/null
error_found=$?
grep "VERIFICATION SUCCESSFUL" ${out_file} >/dev/null
no_bugs=$?
if [ ${timed_out} -eq 0 ]; then
  echo -e "${benchmark}\tTIMEOUT\t${duration}" >>"${out_file}"
elif [ ${error_found} -eq 0 ]; then
  echo -e "${benchmark}\tVER-FALSE\t${duration}" >>"${out_file}"
elif [ ${no_bugs} -eq 0 ]; then
  echo -e "${benchmark}\tVER-TRUE\t${duration}" >>"${out_file}"
else
  echo -e "${benchmark}\tUNKNOWN\t${duration}" >>"${out_file}"
fi

echo "<full_time>  ${duration}</full_time>" >>"${out_file}"
echo "</stats>" >>"${out_file}"
