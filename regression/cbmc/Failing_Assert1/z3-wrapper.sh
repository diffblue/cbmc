#!/bin/sh

# handle output by older Z3 versions where the output was not compatible with
# current SAT solvers

z3 $1 2>&1 | \
  perl -n -e '
    print "s ".uc($1)."ISFIABLE\n" if(/^((un)?sat)\s*$/);
    print "v $_\n" if(/^-?\d+/);
    print "$_\n" if(/^[sv]\s+/);' 2>&1
