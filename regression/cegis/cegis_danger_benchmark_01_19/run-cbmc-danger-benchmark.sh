#!/bin/bash
#export PATH=${PATH//cbmc-5190/cbmc-trunk-synth}
tool=/users/pkesseli/software/cpp/cbmc/cbmc-trunk-diffblue/regression/cbmc-wrapper.sh
#benchmark_dir=${regression_dir}/cegis-cbmc
result_file=$1.cbmc.log
export out_file=$1.cbmc.out
rm ${out_file} 2>/dev/null
timeout_time=300

    start_time=$(date +%s.%N)
    timeout --kill-after=10 ${timeout_time} bash ${tool} --no-unwinding-assertions $1
    end_time=$(date +%s.%N)
    duration=$(echo "${end_time} - ${start_time}" | bc)
    grep "VERIFICATION FAILED" ${out_file} >/dev/null
    error_found=$?
    grep "VERIFICATION SUCCESSFUL" ${out_file} >/dev/null
    no_bugs=$?
    if [ ${error_found} -eq 0 ]; then
      echo -e "${benchmark}\tFALSE\t${duration}" >>"${result_file}"
    elif [ ${no_bugs} -eq 0 ]; then
      echo -e "${benchmark}\tTRUE\t${duration}" >>"${result_file}"
    else
      echo -e "${benchmark}\tUNKNOWN\t${duration}" >>"${result_file}"
    fi
