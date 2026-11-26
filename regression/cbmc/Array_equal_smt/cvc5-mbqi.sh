#!/bin/sh

# cvc5 only reports "sat" for problems in which a universally quantified
# formula must hold when using model-based quantifier instantiation.

exec cvc5 --mbqi "$@"
