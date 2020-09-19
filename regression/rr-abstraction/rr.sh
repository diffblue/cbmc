#!/bin/bash

# whether verify the program or not
CHECK=false

# executables
GOTO_CC=$1
GOTO_INSTRUMENT=$2
CBMC=$3


CBMC_FLAGS="--unwind 4 
            --trace
            --pointer-check"
            # --nondet-static 
            # --div-by-zero-check 
            # --float-overflow-check 
            # --nan-check 
            # --pointer-overflow-check 
            # --undefined-shift-check 
            # --signed-overflow-check 
            # --unsigned-overflow-check 

# compile program into goto-programs
$GOTO_CC -o main.goto main.c
echo "Goto programs built"

#touch main_abst.goto
$GOTO_INSTRUMENT --use-rra spec.json main.goto main-abst.goto
echo "Goto-abst program built"
# check the program
if [ $CHECK = true ]; then
    $CBMC $CBMC_FLAGS main-abst.goto
fi
