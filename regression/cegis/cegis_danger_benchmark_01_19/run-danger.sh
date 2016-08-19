#!/bin/bash
# Experiment script. Copy to "<cbmc_workspace>/regression/". Use as follows:
# ./run-danger.sh [cegis|cegis-no-ranking]

defaultArgs='--cegis-statistics --cegis-genetic main.c'
config1Out='main.cegis-config1.out'
config2Out='main.cegis-config2.out'
config3Out='main.cegis-config3.out'
config4Out='main.cegis-config4.out'
successValue='</stats>'
baseDir=`pwd`

trap '' SIGTERM

config_input=$1
if [ -z "$1" ]; then config_input='cegis'; fi

for config in ${config_input}; do
 resultFile="${baseDir}/${config}.txt"
 truncate -s 0 "${resultFile}"
 for benchmark in ${baseDir}/cegis/cegis_danger_benchmark_*; do
  echo "${benchmark}"
  cd "${benchmark}"
  echo -n `basename ${benchmark}` >>"${resultFile}"
  benchmarkArgs="--cegis-statistics --cegis-genetic main.c"
  if [ "${config}" == "cegis-no-ranking" ]; then
   benchmarkArgs="--danger-no-ranking ${benchmarkArgs}"
  fi
  if grep --quiet 'safety' 'test.desc'; then
   benchmarkArgs="--safety ${benchmarkArgs}"
  else
   benchmarkArgs="--danger ${benchmarkArgs}"
  fi

  truncate -s 0 ${config1Out}
  truncate -s 0 ${config2Out}
  truncate -s 0 ${config3Out}
  truncate -s 0 ${config4Out}

  cegis ${benchmarkArgs} --cegis-parallel-verify >${config1Out} 2>main.cegis.err &
  config1Pid=$!
  cegis ${benchmarkArgs} --cegis-symex-head-start 2 >${config2Out} 2>main.cegis.err &
  config2Pid=$!
  cegis ${benchmarkArgs} --cegis-tournament-select >${config3Out} 2>main.cegis.err &
  config3Pid=$!
  cegis ${benchmarkArgs} --cegis-tournament-select --cegis-symex-head-start 2 >${config4Out} 2>main.cegis.err &
  config4Pid=$!

  config1Stopped=0
  while [ ${config1Stopped} -eq 0 ] || [ ${config2Stopped} -eq 0 ] || [ ${config3Stopped} -eq 0 ] || [ ${config4Stopped} -eq 0 ]; do
   kill -0 ${config1Pid} >/dev/null 2>&1; config1Stopped=$?
   grep --quiet "${successValue}" ${config1Out}; config1Success=$?
   kill -0 ${config2Pid} >/dev/null 2>&1; config2Stopped=$?
   grep --quiet "${successValue}" ${config2Out}; config2Success=$?
   kill -0 ${config3Pid} >/dev/null 2>&1; config3Stopped=$?
   grep --quiet "${successValue}" ${config3Out}; config3Success=$?
   kill -0 ${config4Pid} >/dev/null 2>&1; config4Stopped=$?
   grep --quiet "${successValue}" ${config4Out}; config4Success=$?

   if [ ${config1Success} -eq 0 ] || [ ${config2Success} -eq 0 ] || [ ${config3Success} -eq 0 ] || [ ${config4Success} -eq 0 ]; then
    while [ ${config1Stopped} -eq 0 ] || [ ${config2Stopped} -eq 0 ] || [ ${config3Stopped} -eq 0 ] || [ ${config4Stopped} -eq 0 ]; do
     killall -9 cegis >/dev/null 2>&1
     kill -0 ${config1Pid} >/dev/null 2>&1; config1Stopped=$?
     kill -0 ${config2Pid} >/dev/null 2>&1; config2Stopped=$?
     kill -0 ${config3Pid} >/dev/null 2>&1; config3Stopped=$?
     kill -0 ${config4Pid} >/dev/null 2>&1; config4Stopped=$?
     sleep 10
    done
   fi
   sleep 10
  done

  if [ ${config1Success} -eq 0 ]; then
    echo -n ' config1' >>"${resultFile}"
    outFile=${config1Out}
  elif [ ${config2Success} -eq 0 ]; then
    echo -n ' config2' >>"${resultFile}"
    outFile=${config2Out}
  elif [ ${config3Success} -eq 0 ]; then
    echo -n ' config3' >>"${resultFile}"
    outFile=${config3Out}
  elif [ ${config4Success} -eq 0 ]; then
    echo -n ' config4' >>"${resultFile}"
    outFile=${config4Out}
  else
    echo -n ' none' >>"${resultFile}"
    outFile='none'
  fi

  if [ "${outFile}" == "none" ]; then
   echo "  N/A" >>"${resultFile}"
  else
   tac ${outFile} | grep -P '<full_time>([^<]+)</full_time>' -m1 | sed -E "s/<full_time>([^<]+)<\/full_time>/\\1/" >>"${resultFile}"
  fi

 done
done
