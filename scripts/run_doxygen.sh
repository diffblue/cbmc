#!/bin/bash

# Check doxygen version
EXPECTED_VERSION="1.8.14"
doxygen --version | grep -x $EXPECTED_VERSION > /dev/null
if [ $? -ne 0 ]
then
  echo "WARNING: Using wrong version of doxygen.\
  The list of expected warnings is for version $EXPECTED_VERSION."
fi

# Run doxygen and filter warnings
SCRIPT_FOLDER=`dirname $0`
cd $SCRIPT_FOLDER/../src
doxygen 2>&1 | ../scripts/filter_expected_warnings.py ../scripts/expected_doxygen_warnings.txt
