#!/bin/bash

src=../../../src
goto_cc=$src/goto-cc/goto-cc
goto_instrument=$src/goto-instrument/goto-instrument
cbmc=$src/cbmc/cbmc

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

arch=${arch,,}
strategy=${strategy,,}

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

timeout 180.0s $goto_cc -o $name.gb $name.c
timeout 180.0s $goto_instrument $flag $name.gb ${name}_$arch.gb $strat
timeout 180.0s $cbmc ${name}_$arch.gb
