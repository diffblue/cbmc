#!/bin/bash

set -e

goto_cc=$1
goto_instrument=$2
cbmc=$3
is_windows=$4

shift 4

function usage() {
  echo "Usage: chain architecture [strategy] test_file.c"
  exit 1
}

if [ $# -eq 3 ]
then
  arch=$1
  strategy=$2
  name=`echo $3 | cut -d. -f1`
elif [ $# -eq 2 ]
then
  arch=$1
  strategy=
  name=`echo $2 | cut -d. -f1`
else
  usage
fi

arch=$(echo $arch | tr A-Z a-z)
strategy=$(echo $strategy | tr A-Z a-z)

if [[ "tso|pso|rmo|power|arm|sc|cav11|" =~ "$arch|" ]]
then
  echo "test for $arch"
else
  usage
fi

if [[ "opt" == "$strategy" ]]
then
  strat=--minimum-interference
elif [[ "oepc" == "$strategy" ]]
then
  strat=--one-event-per-cycle
else
  strat=
fi

if [[ "tso|pso|rmo|power|arm|" =~ "$arch" ]]
then
  flag=--mm\ $arch
elif [[ "cav11" == "$arch" ]]
then
  flag=--$arch
else
  flag=
fi

if [[ "${is_windows}" == "true" ]]; then
  $goto_cc "${name}.c" "/Fe${name}.gb"
else
  $goto_cc -o "${name}.gb" "${name}.c"
fi
perl -e 'alarm shift @ARGV; exec @ARGV' 180 "$goto_instrument" $flag "$name.gb" "${name}_$arch.gb" $strat
perl -e 'alarm shift @ARGV; exec @ARGV' 180 "$cbmc" "${name}_$arch.gb"
