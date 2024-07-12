/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SMT2_SMT2_DEC_H
#define CPROVER_SOLVERS_SMT2_SMT2_DEC_H

#include "smt2_conv.h"

class message_handlert;

class smt2_stringstreamt
{
protected:
  std::stringstream stringstream;
};

/*! \brief Decision procedure interface for various SMT 2.x solvers
*/
class smt2_dect : protected smt2_stringstreamt, public smt2_convt
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

protected:
  std::string solver_binary_or_empty;
  message_handlert &message_handler;
  resultt dec_solve(const exprt &) override;

  /// Everything except the footer is cached, so that output files can be
  /// rewritten with varying footers.
  std::stringstream cached_output;

  resultt read_result(std::istream &in);
};

/// Determine whether \p exit_code is an expected exit code for \p solver, i.e.
/// one that does not by itself indicate a failed solver invocation. A zero exit
/// code is always expected; some solvers additionally use a specific non-zero
/// exit code to signal that they emitted an (error ...) response on stdout
/// (which is read back via read_result) while otherwise running successfully.
bool smt2_solver_exit_code_expected(smt2_convt::solvert solver, int exit_code);

#endif // CPROVER_SOLVERS_SMT2_SMT2_DEC_H
