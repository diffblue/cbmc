# Incremental SMT backend

## General usage

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

## Internal code architecture

### Overview of the sequence of data processing and data flow -

1. Other parts of the cbmc code base send `exprt` based expressions to the
decision procedure through the `handle`, `set_to` and `get` member functions.
See the base class `decision_proceduret` for doxygen of these functions.

2. The `smt2_incremental_decision_proceduret` is responsible for holding state
and building commands to send to the solver. It uses `convert_expr_to_smt` for
the state free (pure) portion of the `exprt` to `termt` conversions.

3. `smt2_incremental_decision_proceduret` sends `smt_commandt` to
`smt_piped_solver_processt`. Although `exprt` is broadly equivalent to `termt`,
the terms must be part of a command giving them a broader meaning before they
are sent to the solver.

4. `smt_piped_solver_processt` uses the `smt_to_smt2_string` function to perform
the conversion from the tree structure of the `smt_commandt` into the linear
structure of the string for sending to the solver.

5. `smt_piped_solver_processt` sends `std::string` to `piped_processt`.

6. `piped_processt` has operating system specific implementations which use
POSIX / Windows API calls to send the strings to the solver process via a pipe.
Note that the solver is kept in a operating system separated process, not a
thread. This supports multiprocessing with the solver ingesting commands whilst
the cbmc process continues symex to generate the following commands.

7. `piped_processt` receives output strings from the solver process using OS API
calls and a buffer, when the `smt_piped_solver_processt` requests them.

8. The response strings returned to `smt_solve_processt` are converted into type
less parse trees in the form of raw `irept`s using `smt2irep`. `smt2irep` is
essentially just an S-expression parser.

9. `smt_piped_solver_processt` uses `validate_smt_response` to convert the
`irept` parse tree into either a set of validation errors or a `smt_responset`.
The case of validation errors is considered to be an error with the solver.
Therefore an exception may be thrown for use as user feedback rather than
violating an `INVARIANT` as would be the case for an internal cbmc error.

10. The well sorted `smt_reponset` is then returned to the
`smt2_incremental_decision_proceduret`.

11. In the case of `smt2_incremental_decision_proceduret::get` the response is
expected to be an `smt_get_value_responset`. The decision procedure uses
`construct_value_expr_from_smt` to convert the value term in the response from
the solver into an expression value. This requires information from the decision
procedure about the kind of type the constructed expression should have. The
reason for this is that the smt formula (although well sorted) does not encode
cbmc's notion of types and a given value in SMT terms could correspond to
multiple different types of cbmc expression.

12. The constructed expression can then be returned to the rest of the cbmc code
base outside the decision procedure.
