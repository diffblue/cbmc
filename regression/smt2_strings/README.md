Test Suite for SMT2 String Operations
=====================================

The purpose of this suite is to test the level of string support of CBMC's SMT2
backend.

It can also be used to test the level of string support of any SMT2 solver, by
using a command such as:
```
../test.pl -p -CKFT -c <path_to_solver_binary>
```

(note the `-CKFT` option to consider all testing levels ("CORE", "KNOWNBUG",
"FUTURE", "THOROUGH"), as these are relevant to CBMC only.

More specifically, tests are tagged according to the expected support by the
3rd party solver. The commands below will only run the tests where support is
expected:

CVC4:
```
../test.pl -p -CKFT -X cvc4_bug -c <path_to_cvc4_binary>
```
Note: Most of the string operations are only supported when cvc4 is passed the
`--strings-exp` option. For running the tests, suggest creating a script that
calls cvc4 with `--strings-exp`, and pass the path to that script to the
command above.

Z3:
```
../test.pl -p -CKFT -X z3_bug -c <path_to_z3_binary>
```
