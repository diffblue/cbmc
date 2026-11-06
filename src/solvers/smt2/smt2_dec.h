/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SMT2_SMT2_DEC_H
#define CPROVER_SOLVERS_SMT2_SMT2_DEC_H

#include <solvers/conflict_provider.h>

#include "smt2_conv.h"

#include <set>

class message_handlert;

class smt2_stringstreamt
{
protected:
  std::stringstream stringstream;
};

/*! \brief Decision procedure interface for various SMT 2.x solvers
*/
class smt2_dect : protected smt2_stringstreamt,
                  public smt2_convt,
                  public conflict_providert
{
public:
  smt2_dect(
    const namespacet &_ns,
    const std::string &_benchmark,
    const std::string &_notes,
    const std::string &_logic,
    solvert _solver,
    const std::string &_solver_binary_or_empty,
    message_handlert &_message_handler)
    : smt2_convt(_ns, _benchmark, _notes, _logic, _solver, stringstream),
      solver_binary_or_empty(_solver_binary_or_empty),
      message_handler(_message_handler)
  {
  }

  std::string decision_procedure_text() const override;

  /// Check whether the given expression is in the unsat core
  /// (i.e., was a failed assumption). Only valid after an UNSAT result.
  bool is_in_conflict(const exprt &expr) const override;

protected:
  std::string solver_binary_or_empty;
  message_handlert &message_handler;
  resultt dec_solve(const exprt &) override;

  /// Everything except the footer is cached, so that output files can be
  /// rewritten with varying footers.
  std::stringstream cached_output;

  resultt read_result(std::istream &in);

  /// Set of assumption identifiers reported as failed by the SMT solver
  /// after an UNSAT result. Populated by read_result().
  std::set<std::string> failed_assumptions;
};

#endif // CPROVER_SOLVERS_SMT2_SMT2_DEC_H
