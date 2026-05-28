/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SMT2_SMT2_DEC_H
#define CPROVER_SOLVERS_SMT2_SMT2_DEC_H

#include <solvers/prop/solver_resource_limits.h>

#include "smt2_conv.h"

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
                  public solver_resource_limitst
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

  /// \copydoc solver_resource_limitst::set_time_limit_milliseconds
  /// Honoured for solvers that accept a command-line timeout (Z3, cvc5); for
  /// other SMT2 solvers a warning is logged and the limit is ignored.
  void set_time_limit_milliseconds(uint32_t lim) override
  {
    time_limit_milliseconds = lim;
  }

protected:
  std::string solver_binary_or_empty;
  message_handlert &message_handler;
  uint32_t time_limit_milliseconds = 0;
  resultt dec_solve(const exprt &) override;

  /// Everything except the footer is cached, so that output files can be
  /// rewritten with varying footers.
  std::stringstream cached_output;

  resultt read_result(std::istream &in);
};

#endif // CPROVER_SOLVERS_SMT2_SMT2_DEC_H
