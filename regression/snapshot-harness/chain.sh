#!/bin/bash

set -e

goto_cc=$1
goto_harness=$2
memory_analyzer=$3
cbmc=$4
goto_gcc=$5
entry_point='generated_entry_function'
break_point='checkpoint'

name=${*:$#}
name=${name%.c}
memory_analyzer_symbols=$6
goto_harness_args=${*:7:$#-7}

$goto_cc -o "${name}_cc.gb" "${name}.c"
$goto_gcc -g -std=c11 -o "${name}_gcc.gb" "${name}.c"

$memory_analyzer --symtab-snapshot --json-ui --breakpoint $break_point --symbols ${memory_analyzer_symbols} "${name}_gcc.gb" > "${name}.json"

if [ -e "${name}-mod.gb" ] ; then
  rm -f "${name}-mod.gb"
fi

$goto_harness "${name}_cc.gb" "${name}-mod.gb" --harness-function-name $entry_point --memory-snapshot "${name}.json" ${goto_harness_args}
$cbmc --function $entry_point "${name}-mod.gb" \
  --pointer-check `# because we want to see out of bounds errors` \
  --unwind 11 `# with the way we set up arrays symex can't figure out loop bounds automatically` \
  --unwinding-assertions `# we want to make sure we don't accidentally pass tests because we didn't unwind enough` \
  # cbmc args end
