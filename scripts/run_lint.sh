#!/bin/bash

script_folder=`dirname $0`

$script_folder/run_diff.sh CPPLINT "$@"
