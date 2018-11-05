#!/bin/bash

SCRIPT_FOLDER=`dirname $0`
cd $SCRIPT_FOLDER/../src
doxygen 2>&1 | ../scripts/filter_expected_warnings.py ../scripts/expected_doxygen_warnings.txt
