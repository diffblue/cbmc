#!/bin/bash

set -e

goto_cc=$1
goto_harness=$2
cbmc=$3
is_windows=$4
entry_point='generated_entry_function'

name=${*:$#}
name=${name%.c}
args=${*:5:$#-5}

input_c_file="${name}.c"
input_goto_binary="${name}.gb"
harness_c_file="${name}-harness.c"



if [[ "${is_windows}" == "true" ]]; then
  $goto_cc "$input_c_file"
  mv "${name}.exe" "$input_goto_binary"
else
  $goto_cc -o "$input_goto_binary" "$input_c_file"
fi

if [ -e "$harness_c_file" ] ; then
  rm -f "$harness_c_file"
fi

# `# some comment` is an inline comment - basically, cause bash to execute an empty command
$cbmc --show-goto-functions "$input_goto_binary"
$goto_harness "$input_goto_binary" "$harness_c_file" --harness-function-name $entry_point ${args}
$cbmc --show-goto-functions "$harness_c_file"
$cbmc --function $entry_point "$input_c_file" "$harness_c_file" \
  --pointer-check `# because we want to see out of bounds errors` \
  --unwind 11 `# with the way we set up arrays symex can't figure out loop bounds automatically` \
  --unwinding-assertions `# we want to make sure we don't accidentally pass tests because we didn't unwind enough` \
  # cbmc args end
