#!/bin/bash

# Get a unique number to prevent collision of output files
outputDir=`mktemp -d ./coverage_XXXXX`
if [ $? -ne 0 ]; then
    printf "ERROR: Could not create output directoy"
    exit 1
fi

# Check that the previous command succeded, if not exit.
commandStatus()
{
    if [ $? -ne 0 ]; then
    printf "[ERROR]\n"
    echo "ERROR: See $outputDir/cbmc_coverage.out for more information"
    exit 1
    fi
    printf "[OK]\n"
}

# Check that lcov has been installed
printf "INFO: Checking lcov is installed "
lcov -version > $outputDir/cbmc_coverage.out 2>&1
commandStatus

# Remove any previous build that may not have coverage in it.
printf "INFO: Cleaning CBMC build "
make clean -C ../src >> $outputDir/cbmc_coverage.out 2>&1
commandStatus

printf "INFO: Building CBMC with Code Coverage enabled "
# Run the usual make target with --coverage to add gcov instrumentation
make CXXFLAGS="--coverage" LINKFLAGS="--coverage" -C ../src >> $outputDir/cbmc_coverage.out 2>&1
commandStatus

printf "INFO: Running Regression tests "
# Run regression tests which will collect the coverage metrics and put them in the src files
make >> $outputDir/cbmc_coverage.out 2>&1
printf "[DONE]\n"

printf "INFO: Gathering coverage metrics "
# Gather all of the coverage metrics into a single file
lcov --capture --directory ../src --output-file $outputDir/cbmcCoverage.info >> $outputDir/cbmc_coverage.out 2>&1
commandStatus

printf "INFO: Removing unwanted metrics (for external libaries) "
# Remove the metrics for files that aren't CBMC's source code
lcov --remove $outputDir/cbmcCoverage.info '/usr/*' --output-file $outputDir/cbmcCoverage.info >> $outputDir/cbmc_coverage.out 2>&1
commandStatus

printf "INFO: Creating coverage report "
# Generate the HTML coverage report
genhtml $outputDir/cbmcCoverage.info --output-directory $outputDir/cbmcCoverage >> $outputDir/cbmc_coverage.out 2>&1
commandStatus
echo "INFO: Coverage report is availabe in $outputDir/cbmcCoverage"
