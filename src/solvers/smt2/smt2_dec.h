/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SMT2_SMT2_DEC_H
#define CPROVER_SOLVERS_SMT2_SMT2_DEC_H

#include <fstream>

#include <util/message.h>

#include "smt2_conv.h"

class smt2_stringstreamt
{
protected:
  std::stringstream stringstream;
};

/*! \brief Decision procedure interface for various SMT 2.x solvers
*/
class smt2_dect : protected smt2_stringstreamt,
                  public smt2_convt,
                  public messaget
{
public:
  smt2_dect(
    const namespacet &_ns,
    const std::string &_benchmark,
    const std::string &_notes,
    const std::string &_logic,
    solvert _solver):
    smt2_convt(_ns, _benchmark, _notes, _logic, _solver, stringstream)
  {
  }

  resultt dec_solve() override;
  std::string decision_procedure_text() const override;

protected:
  resultt read_result(std::istream &in);
};

#endif // CPROVER_SOLVERS_SMT2_SMT2_DEC_H
