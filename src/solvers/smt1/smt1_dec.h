/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_SMT_DEC_H
#define CPROVER_PROP_SMT_DEC_H

#include <fstream>

#include "smt1_conv.h"

class smt1_temp_filet
{
public:
  smt1_temp_filet();
  ~smt1_temp_filet();

protected:  
  std::ofstream temp_out;
  std::string temp_out_filename, temp_result_filename;
};

class smt1_dect:protected smt1_temp_filet, public smt1_convt
{
public:
  typedef enum { BOOLECTOR, CVC3, YICES, Z3 } solvert;

  smt1_dect(
    const namespacet &_ns,
    const std::string &_benchmark,
    const std::string &_source,
    const std::string &_logic,
    solvert _solver):
    smt1_temp_filet(),
    smt1_convt(_ns, _benchmark, _source, _logic, temp_out),
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
