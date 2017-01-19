#!/bin/bash

# By default remove temporary files after the run
keep_files=false

# Get a unique number to prevent collision of output files
output_dir=`mktemp -d ./coverage_XXXXX`
if [ $? -ne 0 ]; then
    printf "ERROR: Could not create output directoy"
    exit 1
fi

# Check that the previous command succeded, if not exit.
command_status()
{
    if [ $? -ne 0 ]; then
    printf "[ERROR]\n"
    echo "ERROR: See $output_dir/cbmc_coverage.out for more information"
    exit 1
    fi
    printf "[OK]\n"
}

# Print usage
print_usage()
{
    echo "Usage: $0 [-k]"
    echo "    -k Keep all raw coverage files"
}

#Check the options that the user provided
while getopts ":k" opt
do
    case $opt in
        k)
            keep_files=true
            ;;
        \?)
            echo "ERROR: Invalid option: -$opt"
            print_usage
            exit 1
            ;;
    esac
done

# Check that lcov has been installed
printf "INFO: Checking lcov is installed "
lcov -version > $output_dir/cbmc_coverage.out 2>&1
command_status

# Remove any previous build that may not have coverage in it.
printf "INFO: Cleaning CBMC build "
make clean -C ../src >> $output_dir/cbmc_coverage.out 2>&1
command_status

printf "INFO: Building CBMC with Code Coverage enabled "
# Run the usual make target with --coverage to add gcov instrumentation
make CXXFLAGS="--coverage" LINKFLAGS="--coverage" -C ../src >> $output_dir/cbmc_coverage.out 2>&1
command_status

printf "INFO: Running Regression tests "
# Run regression tests which will collect the coverage metrics and put them in the src files
make >> $output_dir/cbmc_coverage.out 2>&1
printf "[DONE]\n"

printf "INFO: Gathering coverage metrics "
# Gather all of the coverage metrics into a single file
lcov --capture --directory ../src --output-file $output_dir/cbmc_coverage.info >> $output_dir/cbmc_coverage.out 2>&1
command_status

printf "INFO: Removing unwanted metrics (for external libaries) "
# Remove the metrics for files that aren't CBMC's source code
lcov --remove $output_dir/cbmc_coverage.info '/usr/*' --output-file $output_dir/cbmc_coverage.info >> $output_dir/cbmc_coverage.out 2>&1
command_status

printf "INFO: Creating coverage report "
# Generate the HTML coverage report
genhtml $output_dir/cbmc_coverage.info --output-directory $output_dir/cbmc_coverage >> $output_dir/cbmc_coverage.out 2>&1
command_status
echo "INFO: Coverage report is availabe in $output_dir/cbmc_coverage"

if [ $keep_files == false ]; then
    # Remove the temporary coverage files
    printf "INFO: Removing temporary coverage files (1 of 2) "
    find ../ -name "*.gcda" -delete >> $output_dir/cbmc_coverage.out 2>&1
    command_status
    printf "INFO: Removing temporary coverage files (2 of 2) "
    find ../ -name "*.gcno" -delete >> $output_dir/cbmc_coverage.out 2>&1
    command_status
fi
