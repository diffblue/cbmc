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

/*! \brief TO_BE_DOCUMENTED
    \ingroup gr_smt2
*/
class smt2_dect:protected smt2_temp_filet, public smt2_convt
{
public:
  typedef enum { BOOLECTOR, CVC3, YICES, Z3 } solvert;

  smt2_dect(
    const namespacet &_ns,
    const std::string &_benchmark,
    const std::string &_notes,
    const std::string &_logic,
    solvert _solver):
    smt2_temp_filet(),
    smt2_convt(_ns, _benchmark, _notes, _logic, temp_out),
    logic(_logic),
    solver(_solver)
  {
  }
  
  virtual resultt dec_solve();
  virtual std::string decision_procedure_text() const;
  
protected:
  std::string logic;
  solvert solver;

  resultt read_result_boolector(std::istream &in);
  resultt read_result_cvc3(std::istream &in);
  resultt read_result_yices(std::istream &in);
  resultt read_result_z3(std::istream &in);
  
  bool string_to_expr_z3(
    const typet &type, 
    const std::string &value, exprt &e) const;  
};

#endif
