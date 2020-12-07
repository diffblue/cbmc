#!/bin/bash

# whether verify the program or not
CHECK=true

# paths to the benchmark repos
AWS_C_COMMON_PATH="/home/ubuntu/aws-c-common"

# executables
MAKE="make"
GOTO_INSTRUMENT="/home/ubuntu/cbmc/build/bin/goto-instrument"
CBMC="/home/ubuntu/cbmc/build/bin/cbmc"
CBMC_FLAGS="--trace
            --bounds-check
            --conversion-check
            --div-by-zero-check
            --enum-range-check
            --float-overflow-check
            --nan-check
            --pointer-check
            --pointer-overflow-check
            --pointer-primitive-check
            --signed-overflow-check
            --undefined-shift-check
            --unsigned-overflow-check
            --external-sat-solver kissat"

# benchmark name + number of concrete indices
AWS_C_COMMON_TESTS=(
    "aws_array_eq 3"
    "aws_array_eq_c_str 5"
    "aws_array_eq_c_str_ignore_case 5"
    "aws_array_eq_ignore_case 3"
    "aws_byte_buf_eq 6"
    "aws_byte_buf_eq_ignore_case 6"
    "aws_byte_buf_eq_c_str 6"
    "aws_byte_buf_eq_c_str_ignore_case 6"
    "aws_byte_cursor_eq 4"
    "aws_byte_cursor_eq_c_str 5"
    "aws_byte_cursor_eq_c_str_ignore_case 5"
    "aws_byte_cursor_eq_byte_buf 5"
    "aws_byte_cursor_eq_byte_buf_ignore_case 5"
)

cwd=$(pwd)
for testp in "${AWS_C_COMMON_TESTS[@]}"; do
    testl=($testp)
    test=${testl[0]}
    num_ind=${testl[1]}
    let unwind=($num_ind-1)*2
    echo "===== $test ====="
    cd $AWS_C_COMMON_PATH/.cbmc-batch/jobs/$test/
    # compile program into goto-programs
    $MAKE veryclean 2&>1
    $MAKE goto 2&>1
    echo "Goto programs built"
    cd $cwd
    # run goto-instrument to make abstracted goto-programs
    $GOTO_INSTRUMENT --use-rra $cwd/specs/$test.json \
        $AWS_C_COMMON_PATH/.cbmc-batch/jobs/$test/${test}_harness.goto \
        $AWS_C_COMMON_PATH/.cbmc-batch/jobs/$test/${test}_harness_abst.goto
    # print the goto-programs into txts
    rm $AWS_C_COMMON_PATH/.cbmc-batch/jobs/$test/${test}_harness_abst.txt
    $GOTO_INSTRUMENT --show-goto-functions \
        $AWS_C_COMMON_PATH/.cbmc-batch/jobs/$test/${test}_harness_abst.goto \
        >> $AWS_C_COMMON_PATH/.cbmc-batch/jobs/$test/${test}_harness_abst.txt
    # check the program
    if [ $CHECK = true ]; then
        $CBMC $CBMC_FLAGS --unwind $unwind $AWS_C_COMMON_PATH/.cbmc-batch/jobs/$test/${test}_harness_abst.goto
    fi
done
