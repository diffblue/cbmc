#!/bin/bash

# whether verify the program or not
CHECK=true

# executables
bindir="$(pwd)/../../build/bin"
GOTO_CC="$bindir/goto-cc"
GOTO_INSTRUMENT="$bindir/goto-instrument"
CBMC="$bindir/cbmc"

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

ABSTRACTION_TESTS=(
    "test1" 
    "test2" 
    "test3" 
    "test4" 
    "test5" 
    "test6"
    "test7"
    "test8"
    "test9"
    "test10"
    "test11"
)

cwd=$(pwd)
for test in ${ABSTRACTION_TESTS[@]}; do
    echo "===== $test ====="
    cd $test/
    # compile program into goto-programs
    $GOTO_CC -o main.goto main.c
    echo "Goto programs built"
    cd $cwd

    for spec in "$test"/*.json; do
        # run goto-instrument to make abstracted goto-programs
        $GOTO_INSTRUMENT --use-rra $spec \
            $test/main.goto \
            $test/main_abst.goto
        # check the program
        if [ $CHECK = true ]; then
            $CBMC $CBMC_FLAGS $test/main_abst.goto
        fi
    done

done
