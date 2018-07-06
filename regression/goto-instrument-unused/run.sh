# compile test case
# to be called from sub-directories only, to match path to tools
../../../src/goto-cc/goto-cc main.c -o test &> /dev/null; echo $?

../../../src/goto-instrument/goto-instrument --show-unused test
echo $?
