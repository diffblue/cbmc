#!/usr/bin/env bash

# Chain script for tests that exercise repeated invocations of
# goto-instrument on the same goto binary. Distinguishing feature
# compared to the chain.sh scripts under contracts/ and
# contracts-dfcc/: this one runs goto-instrument *twice*. The first
# invocation is expected to succeed and write its output to mod1.gb;
# the second invocation feeds mod1.gb back through goto-instrument
# with a (possibly different) set of arguments.
#
# test.desc layout used by these tests:
#   args1 _ args2 _ cbmc_args
# where args1 are the goto-instrument flags for the first pass,
# args2 are the goto-instrument flags for the second pass, and
# cbmc_args (optional) are passed to a final cbmc invocation on the
# resulting mod2.gb. The first pass is expected to succeed; the
# second pass is the primary item under test (it may succeed or
# deliberately fail, depending on the test).

set -e

goto_cc=$1
goto_instrument=$2
cbmc=$3
is_windows=$4

name=${*:$#}
name=${name%.c}

args=${*:5:$#-5}

# Split args on " _ " into (args1, args2, cbmc_args).
# Note: the literal " _ " token is the field separator, so a goto-instrument
# flag that is itself "_" (none exists today) would be mis-split rather than
# diagnosed. The splitting boilerplate is intentionally duplicated from
# contracts/chain.sh and contracts-dfcc/chain.sh because of the distinct
# run-twice behaviour; factor into a shared helper if these keep diverging.
if [[ "$args" != *" _ "* ]]; then
  echo "contracts-repeat/chain.sh: test.desc args must contain '_' separator" >&2
  exit 1
fi
args1="${args%%" _ "*}"
rest="${args#*" _ "}"
if [[ "$rest" != *" _ "* ]]; then
  args2="$rest"
  args_cbmc=""
else
  args2="${rest%%" _ "*}"
  args_cbmc="${rest#*" _ "}"
fi

if [[ "${is_windows}" == "true" ]]; then
  $goto_cc "${name}.c" "/Fe${name}.gb"
else
  $goto_cc -o "${name}.gb" "${name}.c"
fi

rm -f "${name}-mod1.gb" "${name}-mod2.gb"

# First pass: must succeed.
$goto_instrument ${args1} "${name}.gb" "${name}-mod1.gb"

# Second pass: this is what the test is primarily checking. Run it
# without -e so a non-zero exit doesn't abort chain.sh; record both
# stdout/stderr so test.pl can match against them, and the exit code
# so the test.desc can pin it down via ^EXIT=N$.
set +e
$goto_instrument ${args2} "${name}-mod1.gb" "${name}-mod2.gb"
exit_code=$?
set -e

if [[ -n "${args_cbmc}" && ${exit_code} -eq 0 ]]; then
  $cbmc "${name}-mod2.gb" ${args_cbmc}
fi

exit ${exit_code}
