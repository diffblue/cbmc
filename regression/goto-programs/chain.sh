#!/usr/bin/env bash
set -e
goto_cc=$1
cbmc=$2
is_windows=$3
shift 3

# Handle --chain option: run the specified chain script
if [[ "$1" == "--chain" ]]; then
  shift
  chain_script=$1
  shift
  exec bash "${chain_script}" "${goto_cc}" "${cbmc}" "${is_windows}" "$@"
fi

# Default: just run cbmc with the given options
exec "${cbmc}" "$@"
