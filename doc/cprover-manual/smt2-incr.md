[CPROVER Manual TOC](../)

## SMT 2 incremental backend

CBMC supports many different smt solver backends. This document describes how to use the incremental
smt2 solver. For other solver usages use `cbmc --help`.

The incremental smt2 solver backend of CBMC is a solver-agnostic smt backend that allows the user to
specify which smtlib 2.6 compliant solver CBMC should use. This choice increases the flexibility of
CBMC as the user can easily switch solver at runtime also allowing custom parametrization of the
solver to be used. Further, the backend exploits the incremental mode of the smt solver, so
subsequent incremental SMT solver queries do not require a full re-evaluation of the entire SMT
formula.

### Supported features

The incremental smt2 solver supports the following CBMC C features:

* Integral types (including integers, characters and boolean). These are encoded into smt by using
  bit-vectors,
* Pointers. Encoded by using smt bit-vectors. This includes support for pointers to both stack and
  heap-allocated memory,
* Arrays. Encoded by using smt array theory.

Currently, unsupported features include floating-point types, structs and unions.

For more details on which features are supported see regression
tests in [`regression/cbmc-incr-smt2`](../regression/cbmc-incr-smt2).

The backend has been tested with these instrumentation passes:

* `--bounds-check`,
* `--conversion-check`,
* `--div-by-zero-check`,
* `--pointer-check`,
* `--pointer-overflow-check`,
* `--signed-overflow-check`,
* `--unsigned-overflow-check`,
* `--unwinding-assertions`.

### Requisites

To run the incremental smt2 backend it is necessary to have an smt solver that:

* is runnable from the command line,
* supports interactive mode from the command line,
* supports smtlib 2.6 input,
* supports incremental mode.

Because of the way supported features are encoded the smt solver should be capable to handle arrays,
bit-vectors, uninterpreted functions and quantifiers. Also, the solver should work with the `ALL`
smt theory.

At the time of writing the smt solvers tested in CI
are [Z3](https://github.com/Z3Prover/z3)
and [CVC5](https://cvc5.github.io/).

### Usage

To use the incremental SMT2 backend it is enough to add the `--incremental-smt2-solver` argument to
the CBMC command line followed by the command to invoke the chosen solver using smtlib 2.6 input in
interactive mode.

Note that the use of the `--slice-formula` option is recommended at this time to slice out
unnecessary code (that may not be supported at the moment) and this can also improve performance.

Here are two examples to show how to analyse a file `program.c` using Z3 and CVC5 solvers.

To use the Z3 SMT solver:

```shell 
cbmc --slice-formula --incremental-smt2-solver 'z3 -smt2 -in' program.c
```

If `z3` is not on the `PATH`, then it is enough to replace `'z3 -smt2 -in'`
with `'<command-to-execute-z3> -smt2 -in'`,

Similarly to execute CBMC using the CVC5 solver:

```shell
cbmc --slice-formula --incremental-smt2-solver 'cvc5 --lang=smtlib2.6 --incremental' program.c
```

As the command to execute the solver is left to the user, it is possible to fine-tune it by passing
extra parameters (when the solver allows so). For example Z3 allows to set certain parameters by
adding `param_name=value` to the command line, so to use the Z3 solver with `well_sorted_check`
property set to `false` the following has to be run:

```shell
cbmc --slice-formula --incremental-smt2-solver 'z3 -smt2 -in well_sorted_check=false' program.c
```

### Examples

Given a C program `program.c` as follows:

```C
int main()
{
  int x, y;
  if(x != 0)
    __CPROVER_assert(y != 4, "Assert of inequality to 4.");
  else
    __CPROVER_assert(y != 2, "Assert of inequality to 2.");
  int z = y;
  return 0;
}
```

To analyze it we should run:

```shell
cbmc --incremental-smt2-solver 'z3 -smt2 -in' --slice-formula program.c
```

We will get the verification results as follows:

```text
CBMC version 5.70.0 (cbmc-5.70.0-53-g20535ad14d) 64-bit x86_64 macos
Parsing program.c
Converting
Type-checking program
Generating GOTO Program
Adding CPROVER library (x86_64)
Removal of function pointers and virtual functions
Generic Property Instrumentation
Running with 8 object bits, 56 offset bits (default)
Starting Bounded Model Checking
Runtime Symex: 0.00168879s
size of program expression: 45 steps
slicing removed 23 assignments
Generated 2 VCC(s), 2 remaining after simplification
Runtime Postprocess Equation: 2.1865e-05s
Passing problem to incremental SMT2 solving via "z3 -smt2 -in"
```

Note here that the solver used by CBMC is `"z3 -smt2 -in"` as specified by the user.

```text
[continues]
converting SSA
Runtime Convert SSA: 0.00130809s
Running incremental SMT2 solving via "z3 -smt2 -in"
Runtime Solver: 0.0738685s
Runtime decision procedure: 0.0765297s
Running incremental SMT2 solving via "z3 -smt2 -in"
Runtime Solver: 0.00535358s
Runtime decision procedure: 0.00570765s

** Results:
program.c function main
[main.assertion.1] line 5 Assert of inequality to 4.: FAILURE
[main.assertion.2] line 7 Assert of inequality to 2.: FAILURE

** 2 of 2 failed (3 iterations)
VERIFICATION FAILED
```

As expected CBMC returns `FAILURE` for both assertions at lines `5` and `7`.

The incremental smt2 backend also supports trace generation, so to get a trace that fails the
assertions the `--trace` argument should be added, so the command to run is:

```shell
cbmc --incremental-smt2-solver 'z3 -smt2 -in' --slice-formula --trace program.c
```

This will append the trace to CBMC's output as follows:

```text
CBMC version 5.70.0 (cbmc-5.70.0-53-g20535ad14d) 64-bit x86_64 macos
Parsing program.c
[...]
[main.assertion.1] line 5 Assert of inequality to 4.: FAILURE
[main.assertion.2] line 7 Assert of inequality to 2.: FAILURE

Trace for main.assertion.1:

State 6 file program.c function main line 3 thread 0
----------------------------------------------------
  x=-1 (11111111 11111111 11111111 11111111)

State 7 file program.c function main line 3 thread 0
----------------------------------------------------
  y=4 (00000000 00000000 00000000 00000100)

Violated property:
  file program.c function main line 5 thread 0
  Assert of inequality to 4.
  y != 4



Trace for main.assertion.2:

State 6 file program.c function main line 3 thread 0
----------------------------------------------------
  x=0 (00000000 00000000 00000000 00000000)

State 7 file program.c function main line 3 thread 0
----------------------------------------------------
  y=2 (00000000 00000000 00000000 00000010)

Violated property:
  file program.c function main line 7 thread 0
  Assert of inequality to 2.
  y != 2



** 2 of 2 failed (3 iterations)
VERIFICATION FAILED
```
