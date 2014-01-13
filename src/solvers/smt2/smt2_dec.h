/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_SMT2_DEC_H
#define CPROVER_PROP_SMT2_DEC_H

/*! \defgroup gr_smt2 SMT-LIB 2.x Interface */

#include <fstream>

#include "smt2_conv.h"

class smt2_temp_filet
{
public:
  smt2_temp_filet();
  ~smt2_temp_filet();

protected:  
  std::ofstream temp_out;
  std::string temp_out_filename, temp_result_filename;
};

/*! \brief Decision procedure interface for various SMT 2.x solvers
    \ingroup gr_smt2
*/
class smt2_dect:protected smt2_temp_filet, public smt2_convt
{
public:
  smt2_dect(
    const namespacet &_ns,
    const std::string &_benchmark,
    const std::string &_notes,
    const std::string &_logic,
    solvert _solver):
    smt2_temp_filet(),
    smt2_convt(_ns, _benchmark, _notes, _logic, _solver, temp_out)
  {
  }

  virtual resultt dec_solve();
  virtual std::string decision_procedure_text() const;
  
  // yes, we are incremental!
  virtual bool has_set_assumptions() const { return true; }
  
protected:
  resultt read_result_boolector(std::istream &in);
  resultt read_result_cvc3(std::istream &in);
  resultt read_result_mathsat(std::istream &in);
  resultt read_result_yices(std::istream &in);
  resultt read_result_z3(std::istream &in);
  
  bool string_to_expr_z3(
    const typet &type, 
    const std::string &value, exprt &e) const;  
};

#endif
