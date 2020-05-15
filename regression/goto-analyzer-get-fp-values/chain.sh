#!/bin/bash

GotoAnalyzerPath=$1
echo "GotoAnalyzerPath = $GotoAnalyzerPath"
GotoCCPath=$2
echo "GotoCCPath = $GotoCCPath"
GotoInstrumentPath=$3
echo "GotoInstrumentPath = $GotoInstrumentPath"
CBMCPath=$4
echo "CBMCPath = $CBMCPath"
is_windows=$5
echo "is_windows = $is_windows"
TestCPath=$6
echo "TestCPath = $TestCPath"
TestJSONPath=$(mktemp $(basename $TestCPath).restrictions.XXXXX.json);
echo "TestJSONPath = $TestJSONPath"

GotoBinaryPath="$(mktemp $(basename $TestCPath).XXXXX.gb)"
if [[ "$is_windows" == "true" ]]; then
  GotoBinaryPath="$GotoBinaryPath.exe"
fi
echo "GotoBinaryPath = $GotoBinaryPath"

GotoBinaryModPath="$(mktemp $(basename $TestCPath).XXXXX.mod.gb)"
if [[ "$is_windows" == "true" ]]; then
  GotoBinaryModPath="$GotoBinaryModPath.exe"
fi
echo "GotoBinaryModPath = $GotoBinaryModPath"

# Set up pipeline
# goto-cc produces temporary goto binary from C file
# goto-analyzer produces json file with restrictions
# goto-instrument produces new gb with old gb + restrictions
# cbmc runs on final gb

# purpose: This lets us test end-to-end that all stages of the pipeline are compatible with
# each other, and that they produce the output we expect

echo ">>> Compiling $TestCPath to $GotoBinaryPath"
if [[ "${is_windows}" == "true" ]]; then
  $GotoCCPath $TestCPath "/Fe$GotoBinaryPath"
else
  $GotoCCPath $TestCPath -o $GotoBinaryPath
fi

echo ">>> Analyzing $GotoBinaryPath to get restrictions into $TestJSONPath"
$GotoAnalyzerPath \
   '--get-function-pointer-values' $TestJSONPath \
   $GotoBinaryPath

echo ">>> Instrumenting $GotoBinaryPath with $TestJSONPath to get $GotoBinaryModPath"
$GotoInstrumentPath \
  --function-pointer-restrictions-file $TestJSONPath \
  $GotoBinaryPath $GotoBinaryModPath

echo ">>> Analysing $GotoBinaryModPath"
$CBMCPath $GotoBinaryModPath --pointer-check

echo "<<<<  Restrictions JSON"
cat $TestJSONPath
echo ">>>>"

rm $TestJSONPath
rm $GotoBinaryPath
rm $GotoBinaryModPath
