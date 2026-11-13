/*******************************************************************\

Module: SMT2 decision procedure for cprover state encoding

Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_CPROVER_CPROVER_SMT2_DEC_H
#define CPROVER_CPROVER_CPROVER_SMT2_DEC_H

#include <solvers/smt2/smt2_dec.h>

#include <string>

/// SMT2 decision procedure configured for cprover's state encoding.
/// Uses datatypes for structs (instead of bitvector flattening) to
/// support mathematical types (integer, real, string).
///
/// The emitted SMT2 uses solvert::GENERIC, i.e. standard SMT-LIBv2 without
/// solver-specific options or encodings, so that any SMT2 binary configured
/// via --external-smt2-solver (z3, cvc5, ...) can discharge the queries.  This
/// trades solver-specific tuning for portability.
class cprover_smt2_dect : public smt2_dect
{
public:
  cprover_smt2_dect(
    const namespacet &_ns,
    const std::string &_solver_binary,
    message_handlert &_message_handler)
    : smt2_dect(
        _ns,
        "",
        "cprover",
        "ALL",
        smt2_convt::solvert::GENERIC,
        _solver_binary,
        _message_handler)
  {
    use_array_of_bool = true;
    use_as_const = true;
    use_datatypes = true;
  }
};

#endif // CPROVER_CPROVER_CPROVER_SMT2_DEC_H
