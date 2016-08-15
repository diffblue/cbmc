#!/bin/bash
defaultArgs='--cegis-statistics --cegis-genetic main.c'
cegisOut='main.cegis.out'
cegisHeadStartOut='main.cegis-symex-head-start.out'
cegisTournamentOut='main.cegis-tournament-select.out'
cegisHeadStartTournamentOut='main.cegis-symex-head-start-tournament-select.out'
config5Out='main.cegis-config5.out'
config6Out='main.cegis-config6.out'
config7Out='main.cegis-config7.out'
config8Out='main.cegis-config8.out'
successValue='</stats>'
baseDir=`pwd`

trap '' SIGTERM

#for config in 'cegis' 'cegis-no-ranking'; do
for config in 'cegis'; do
 resultFile="${baseDir}/${config}.txt"
 #truncate -s 0 "${resultFile}"
 #for benchmark in ${baseDir}/${config}/cegis_danger_benchmark_*; do
 for benchmark in ${baseDir}/${config}/cegis_danger_benchmark_01_19/; do
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

  truncate -s 0 ${cegisOut}
  truncate -s 0 ${cegisHeadStartOut}
  truncate -s 0 ${cegisTournamentOut}
  truncate -s 0 ${cegisHeadStartTournamentOut}
  truncate -s 0 ${config5Out}
  truncate -s 0 ${config6Out}
  truncate -s 0 ${config7Out}
  truncate -s 0 ${config8Out}

  ../../run-cbmc-danger-benchmark.sh ${benchmark}/main.c &
  cbmcPid=$!
  cegis ${benchmarkArgs} >${cegisOut} 2>main.cegis.err &
  #../../sleep-echo.sh 10 1>${cegisOut} &
  cegisPid=$!
  cegis ${benchmarkArgs} --die --cegis-tournament-select >${cegisHeadStartOut} 2>main.cegis-symex-head-start.err &
  #../../sleep-echo.sh 100 1>${cegisHeadStartOut} &
  cegisSymexHeadStartPid=$!
  cegis ${benchmarkArgs} --cegis-symex-head-start 2 >${cegisTournamentOut} 2>main.cegis-tournament-select.err &
  #../../sleep-echo.sh 100 1>${cegisTournamentOut} & # unnecessary
  cegisTournamentPid=$!
  cegis ${benchmarkArgs} --cegis-symex-head-start 2 --cegis-tournament-select >${cegisHeadStartTournamentOut} 2>main.cegis-symex-head-start-tournament-select.err & # unnecessary
  #../../sleep-echo.sh 100 1>${cegisHeadStartTournamentOut} &
  cegisSymexHeadStartTournamentPid=$!
  cegis ${benchmarkArgs} --cegis-symex-head-start 3 --cegis-tournament-select --cegis-parallel-verify >${config5Out} 2>main.cegis-config5.err &
  #../../sleep-echo.sh 100 1>${cegisHeadStartTournamentOut} & # unnecessary
  config5Pid=$!
  cegis ${benchmarkArgs} --cegis-symex-head-start 1 >${config6Out} 2>main.cegis-config6.err &
  #../../sleep-echo.sh 100 1>${cegisHeadStartTournamentOut} & # unnecessary
  config6Pid=$!
  cegis ${benchmarkArgs} --cegis-symex-head-start 3 --cegis-parallel-verify >${config7Out} 2>main.cegis-config7.err &
  #../../sleep-echo.sh 100 1>${cegisHeadStartTournamentOut} & # unnecessary
  config7Pid=$!
  cegis ${benchmarkArgs} --cegis-symex-head-start 1 --cegis-tournament-select >${config8Out} 2>main.cegis-config8.err &
  #../../sleep-echo.sh 100 1>${cegisHeadStartTournamentOut} &
  config8Pid=$!

  cegisStopped=0
  #while [ ${cegisStopped} -eq 0 ] || [ ${cegisSymexHeadStartStopped} -eq 0 ] || [ ${cegisTournamentStopped} -eq 0 ]; do
  while [ ${cegisStopped} -eq 0 ] || [ ${cegisSymexHeadStartStopped} -eq 0 ] || [ ${cegisTournamentStopped} -eq 0 ] || [ ${cegisSymexHeadStartTournamentStopped} -eq 0 ] || [ ${config5Stopped} -eq 0 ] || [ ${config6Stopped} -eq 0 ] || [ ${config7Stopped} -eq 0 ] || [ ${config8Stopped} -eq 0 ] || [ ${cbmcStopped} -eq 0 ]; do
   kill -0 ${cegisPid} >/dev/null 2>&1; cegisStopped=$?
   grep --quiet "${successValue}" ${cegisOut}; cegisSuccess=$?
   kill -0 ${cegisSymexHeadStartPid} >/dev/null 2>&1; cegisSymexHeadStartStopped=$?
   grep --quiet "${successValue}" ${cegisHeadStartOut}; cegisSymexHeadStartSuccess=$?
   kill -0 ${cegisTournamentPid} >/dev/null 2>&1; cegisTournamentStopped=$?
   grep --quiet "${successValue}" ${cegisTournamentOut}; cegisTournamentSuccess=$?
   kill -0 ${cegisSymexHeadStartTournamentPid} >/dev/null 2>&1; cegisSymexHeadStartTournamentStopped=$?
   grep --quiet "${successValue}" ${cegisHeadStartTournamentOut}; cegisSymexHeadStartTournamentSuccess=$?
   kill -0 ${config5Pid} >/dev/null 2>&1; config5Stopped=$?
   grep --quiet "${successValue}" ${config5Out}; config5Success=$?
   kill -0 ${config6Pid} >/dev/null 2>&1; config6Stopped=$?
   grep --quiet "${successValue}" ${config6Out}; config6Success=$?
   kill -0 ${config7Pid} >/dev/null 2>&1; config7Stopped=$?
   grep --quiet "${successValue}" ${config7Out}; config7Success=$?
   kill -0 ${config8Pid} >/dev/null 2>&1; config8Stopped=$?
   grep --quiet "${successValue}" ${config8Out}; config8Success=$?
   kill -0 ${cbmcPid} >/dev/null 2>&1; cbmcStopped=$?
   grep --quiet "VERIFICATION" ${config8Out}; cbmcSuccess=$?

   #if [ ${cegisSuccess} -eq 0 ] || [ ${cegisSymexHeadStartSuccess} -eq 0 ] || [ ${cegisTournamentSuccess} -eq 0 ]; then
   if [ ${cegisSuccess} -eq 0 ] || [ ${cegisSymexHeadStartSuccess} -eq 0 ] || [ ${cegisTournamentSuccess} -eq 0 ] || [ ${cegisSymexHeadStartTournamentSuccess} -eq 0 ] || [ ${config5Success} -eq 0 ] || [ ${config6Success} -eq 0 ] || [ ${config7Success} -eq 0 ] || [ ${config8Success} -eq 0 ] || [ ${cbmcSuccess} -eq 0 ]; then
    #while [ ${cegisStopped} -eq 0 ] || [ ${cegisSymexHeadStartStopped} -eq 0 ] || [ ${cegisTournamentStopped} -eq 0 ]; do
    while [ ${cegisStopped} -eq 0 ] || [ ${cegisSymexHeadStartStopped} -eq 0 ] || [ ${cegisTournamentStopped} -eq 0 ] || [ ${cegisSymexHeadStartTournamentStopped} -eq 0 ] || [ ${config5Stopped} -eq 0 ] || [ ${config6Stopped} -eq 0 ] || [ ${config7Stopped} -eq 0 ] || [ ${config8Stopped} -eq 0 ] || [ ${cbmcStopped} -eq 0 ]; do
     killall -9 cegis >/dev/null 2>&1
     killall -9 cbmc >/dev/null 2>&1
     killall timeout >/dev/null 2>&1
     kill -0 ${cegisPid} >/dev/null 2>&1; cegisStopped=$?
     kill -0 ${cegisSymexHeadStartPid} >/dev/null 2>&1; cegisSymexHeadStartStopped=$?
     kill -0 ${cegisTournamentPid} >/dev/null 2>&1; cegisTournamentStopped=$?
     kill -0 ${cegisSymexHeadStartTournamentPid} >/dev/null 2>&1; cegisSymexHeadStartTournamentStopped=$?
     kill -0 ${config5Pid} >/dev/null 2>&1; config5Stopped=$?
     kill -0 ${config6Pid} >/dev/null 2>&1; config6Stopped=$?
     kill -0 ${config7Pid} >/dev/null 2>&1; config7Stopped=$?
     kill -0 ${config8Pid} >/dev/null 2>&1; config8Stopped=$?
     kill -0 ${cbmcPid} >/dev/null 2>&1; cbmcStopped=$?
     sleep 10
    done
   fi
   sleep 10
  done

  if [ ${cegisSuccess} -eq 0 ]; then
    echo -n ' base' >>"${resultFile}"
    outFile=${cegisOut}
  elif [ ${cegisSymexHeadStartSuccess} -eq 0 ]; then
    echo -n ' symex-head-start' >>"${resultFile}"
    outFile=${cegisHeadStartOut}
  elif [ ${cegisTournamentSuccess} -eq 0 ]; then
    echo -n ' tournament' >>"${resultFile}"
    outFile=${cegisTournamentOut}
  elif [ ${cegisSymexHeadStartTournamentSuccess} -eq 0 ]; then
    echo -n ' tournament-symex-head-start' >>"${resultFile}"
    outFile=${cegisHeadStartTournamentOut}
  elif [ ${config5Success} -eq 0 ]; then
    echo -n ' config5' >>"${resultFile}"
    outFile=${config5Out}
  elif [ ${config6Success} -eq 0 ]; then
    echo -n ' config6' >>"${resultFile}"
    outFile=${config6Out}
  elif [ ${config7Success} -eq 0 ]; then
    echo -n ' config7' >>"${resultFile}"
    outFile=${config7Out}
  elif [ ${config8Success} -eq 0 ]; then
    echo -n ' config8' >>"${resultFile}"
    outFile=${config8Out}
  elif [ ${cbmcSuccess} -eq 0 ]; then
    echo -n ' cbmc' >>"${resultFile}"
    outFile='none'
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
