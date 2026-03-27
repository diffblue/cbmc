#!/bin/sh
# Chain script for orphan solver process test.
# test.pl passes the test input file as $1; we run test_orphan.sh
# from the same directory.
dir=$(dirname "$0")
cd "$dir"
exec ./test_orphan.sh
