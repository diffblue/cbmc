#!/bin/bash

set -e

if [ -z "$BENCHEXEC" ]
then
  # default path to benchexec is set to a value that works for me(TM)
  BENCHEXEC=~/Desktop/benchexec.git
fi

categories=""

for d in "$@"
do
  c=$(echo $d/release/logs-* | tr ' ' '\n' | sed 's/.*logs-//')
  categories=$(echo $categories $c | tr ' ' '\n' | sort | uniq)
done

official_logs="
2017-01-11_1131.results.sv-comp17.ConcurrencySafety-Main.xml.bz2
2017-01-11_1020.results.sv-comp17.MemSafety-Arrays.xml.bz2.merged.xml.bz2
2017-01-11_1020.results.sv-comp17.MemSafety-Heap.xml.bz2.merged.xml.bz2
2017-01-11_1020.results.sv-comp17.MemSafety-LinkedLists.xml.bz2.merged.xml.bz2
2017-01-11_1020.results.sv-comp17.MemSafety-Other.xml.bz2.merged.xml.bz2
2017-01-11_1354.results.sv-comp17.Overflows-BitVectors.xml.bz2.merged.xml.bz2
2017-01-11_1354.results.sv-comp17.Overflows-Other.xml.bz2.merged.xml.bz2
2017-01-10_1721.results.sv-comp17.ReachSafety-Arrays.xml.bz2.merged.xml.bz2
2017-01-10_1721.results.sv-comp17.ReachSafety-BitVectors.xml.bz2.merged.xml.bz2
2017-01-10_1721.results.sv-comp17.ReachSafety-ControlFlow.xml.bz2.merged.xml.bz2
2017-01-10_1721.results.sv-comp17.ReachSafety-ECA.xml.bz2.merged.xml.bz2
2017-01-10_1721.results.sv-comp17.ReachSafety-Floats.xml.bz2.merged.xml.bz2
2017-01-10_1721.results.sv-comp17.ReachSafety-Heap.xml.bz2.merged.xml.bz2
2017-01-10_1721.results.sv-comp17.ReachSafety-Loops.xml.bz2.merged.xml.bz2
2017-01-10_1721.results.sv-comp17.ReachSafety-ProductLines.xml.bz2.merged.xml.bz2
2017-01-10_1721.results.sv-comp17.ReachSafety-Recursive.xml.bz2.merged.xml.bz2
2017-01-10_1721.results.sv-comp17.ReachSafety-Sequentialized.xml.bz2.merged.xml.bz2
2017-01-11_1020.results.sv-comp17.Systems_BusyBox_MemSafety.xml.bz2.merged.xml.bz2
2017-01-10_1721.results.sv-comp17.Systems_DeviceDriversLinux64_ReachSafety.xml.bz2.merged.xml.bz2
"

for c in $categories
do
  if [ ! -s official-sv-comp-17/*$c*.xml.bz2 ]
  then
    suffix=$(echo $official_logs | tr ' ' '\n' | grep "sv-comp17\.$c\.xml\.bz2" || true)
    if [ -z "$suffix" ]
    then
      echo "No log known for $c"
      srcs=""
    else
      wget \
        http://sv-comp.sosy-lab.org/2017/results/results-verified/cbmc.$suffix \
        -P official-sv-comp-17/
      srcs="official-sv-comp-17/*$c*.xml.bz2"
    fi
  else
    srcs="official-sv-comp-17/*$c*.xml.bz2"
  fi

  for d in "$@"
  do
    if [ -s $d/release/logs-$c/*.bz2 ]
    then
      srcs="$srcs $d/release/logs-$c/*.bz2"
    fi
  done

  if [ -n "$srcs" ]
  then
    python3 $BENCHEXEC/bin/table-generator -n $c $srcs
  fi
done
