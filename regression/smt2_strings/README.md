Test Suite for SMT2 String Operations
=====================================

The purpose of this suite is to test the level of string support of CBMC's SMT2
backend.

It can also be used to test the level of string support of any SMT2 solver, by
using a command such as:
```
../test.pl -p -F -c <path_to_solver_binary>
```

(note the `-F` option to consider all tests tagged as "FUTURE").

