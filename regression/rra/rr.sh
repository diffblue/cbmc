#!/bin/bash

# whether verify the program or not
CHECK=true

# executables
GOTO_CC=$1
GOTO_INSTRUMENT=$2
CBMC=$3

name=${*:$#}
args=${*:4:$#-4}


CBMC_FLAGS="--trace
            --pointer-check"

# compile program into goto-programs
$GOTO_CC -o main.goto main.c
echo "Goto programs built"

#touch main_abst.goto
$GOTO_INSTRUMENT --use-rra $(pwd)/spec.json $(pwd)/main.goto $(pwd)/main-abst.goto
echo "Goto-abst program built"
# check the program
if [ $CHECK = true ]; then
    $CBMC $CBMC_FLAGS --unwind 10 $PWD/main-abst.goto
fi
