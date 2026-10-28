#!/bin/sh

# A wrapper as used with --external-smt2-solver: it chooses its own cvc5
# options, and CBMC must not add any beyond --lang smtlib.

for arg in "$@" ; do
  case "$arg" in
    --arrays-exp|--fp-exp|--no-fmf-bound)
      echo "unexpected option $arg" >&2
      exit 1
      ;;
  esac
done

exec cvc5 --arrays-exp "$@"
