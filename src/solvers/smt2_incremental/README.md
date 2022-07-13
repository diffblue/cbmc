# Incremental SMT backend

CBMC comes with a solver-agnostic incremental SMT backend.

The SMT incremental backend supports the following `C` features:

- Integers (via Bit vector arithmetics)
- Pointers
- Arrays (support is currently incomplete)

Primitive not supported are:

- Floating point values and arithmetics
- Structs

Usage of the incremental SMT backend requires a SMT solver compatible with
incremental SMTlib v2.6 formatted input from the standard input and that
supports the `QF_AUFBV` (Quantifier Free Array Uninterpreted Functions and Bit
Vectors) logic.

To use this functionality it is enough to add the argument
`--incremental-smt2-solver <cmd>` where `<cmd>` is the command to invoke the SMT
solver of choice using the incremental mode and accepting input from the
standard input.

Examples of invocations with various solvers:

1. `--incremental-smt2-solver 'z3 -smt2 -in'` to use the Z3 solver.
2. `--incremental-smt2-solver 'cvc5 --lang=smtlib2.6 --incremental'` to use the
   CVC5 solver.

The new incremental SMT backend has been designed to interoperate with external
solvers, so the solver name must be in the `PATH` or an executable with full
path must be provided.

Due to lack of support for conversion of `array_of` expressions that are added
by CBMC in the before the new SMT backend is invoked, it is necessary to supply
an extra argument `--slice-formula` so that instances of `arrayof_exprt` are
removed from the formula to be converted.

As we move forward with our array-support implementation, we anticipate that the
need for this extra flag will be diminished.
