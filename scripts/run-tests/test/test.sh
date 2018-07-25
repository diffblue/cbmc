#!/bin/bash

ulimit -v 8000000

DIR=$(readlink --canonicalize $(dirname $0))
cd $DIR

#
# Gather data test
#

mkdir -p test1/test2/test3
echo 'a' > test1/test2/test3/test1.txt
echo 'b' > test1/test2/test3/test2.txt
mkdir test1/test2/test4
echo 'c' > test1/test2/test4/test1.txt
mkdir test1/test2/test5
echo 'd' > test1/test2/test5/test2.txt
mkdir test1/test2/test6

./gather_data_test.py --output-root test1

#
# Run tests test 1
#

LEN=${#HOME}
if [ "$HOME" != "${DIR::$LEN}" ]; then
  exit 1  
fi

RPATH="~${DIR:$LEN}"

mkdir input
touch input/file1
touch input/file2
touch input/file3
touch input/file4
mkdir input/dir1
touch input/dir1/file5
touch input/dir1/file6

touch /tmp/file7
touch /tmp/file8
tar cf input/files.tar /tmp/file7 /tmp/file8
bzip2 input/files.tar

echo \
"^/input/file1
${RPATH}/input/file2
${DIR}/input/file3
${DIR}/input/file4
${DIR}/input/dir1
${DIR}/input/files.tar.bz2" \
> input1.txt

./run_tests_test.py --test 2 --input-file input1.txt --analysis-root ar_test1 \
  --output-root or_test1

#
# Run tests test 2
#

mkdir input2
touch input2/file

echo '^/input2/file' > input2.txt

./run_tests_test.py --test 1 --input-file input2.txt --analysis-root ar_test2 \
  --output-root or_test2

