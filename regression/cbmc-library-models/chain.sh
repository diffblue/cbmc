#!/usr/bin/env bash
# usage: chain.sh CBMC [CBMC OPTIONS...] SOURCE
# Preprocesses the C library models into a directory with
# `--dump-c-library-models', replaces any of them by the `.i' files of the
# test's directory (to tell whether a model comes from the directory), and
# runs cbmc on SOURCE with `--c-library-models' and the given options.
# Options before ` _ ' are used for the dump, too.

set -e

cbmc=$1
source_file=${*:$#}
args=${*:2:$#-2}

if [[ "$args" != *" _ "* ]]
then
  args_dump=""
  args_cbmc=$args
else
  args_dump="${args%%" _ "*}"
  args_cbmc="${args#*" _ "}"
fi

models=models.dir
rm -rf "${models}"
# the directory is not left in the source tree (CI checks that the tree is
# clean after the tests)
trap 'rm -rf "${models}"' EXIT
# shellcheck disable=SC2086
$cbmc ${args_dump} --dump-c-library-models "${models}" > /dev/null
for model in *.i
do
  [ -e "${model}" ] && cp "${model}" "${models}/"
done
# shellcheck disable=SC2086
$cbmc ${args_dump} ${args_cbmc} --c-library-models "${models}" "${source_file}"
