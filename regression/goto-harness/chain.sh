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

if [[ "${is_windows}" == "true" ]]; then
  $goto_cc "${name}.c"
  mv "${name}.exe" "${name}.gb"
else
  $goto_cc -o "${name}.gb" "${name}.c"
fi

if [ -e "${name}-mod.gb" ] ; then
  rm -f "${name}-mod.gb"
fi

# `# some comment` is an inline comment - basically, cause bash to execute an empty command
$cbmc --show-goto-functions "${name}.gb"
$goto_harness "${name}.gb" "${name}-mod.gb" --harness-function-name $entry_point ${args}
$cbmc --show-goto-functions "${name}-mod.gb"
$cbmc --function $entry_point "${name}-mod.gb" \
  --pointer-check `# because we want to see out of bounds errors` \
  --unwind 11 `# with the way we set up arrays symex can't figure out loop bounds automatically` \
  --unwinding-assertions `# we want to make sure we don't accidentally pass tests because we didn't unwind enough` \
  # cbmc args end
