/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SMT1_SMT1_DEC_H
#define CPROVER_SOLVERS_SMT1_SMT1_DEC_H

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

/*! \brief Decision procedure interface for various SMT 1.x solvers
*/
class smt1_dect:protected smt1_temp_filet, public smt1_convt
{
public:
  smt1_dect(
    const namespacet &_ns,
    const std::string &_benchmark,
    const std::string &_source,
    const std::string &_logic,
    solvert _solver):
    smt1_temp_filet(),
    smt1_convt(_ns, _benchmark, _source, _logic, _solver, temp_out),
    logic(_logic),
    dec_solve_was_called(false)
  {
  }

  virtual resultt dec_solve();
  virtual std::string decision_procedure_text() const;

protected:
  std::string logic;
  bool dec_solve_was_called;

  resultt read_result_boolector(std::istream &in);
  resultt read_result_cvc3(std::istream &in);
  resultt read_result_opensmt(std::istream &in);
  resultt read_result_mathsat(std::istream &in);
  resultt read_result_yices(std::istream &in);
  resultt read_result_z3(std::istream &in);

  bool string_to_expr_z3(
    const typet &type,
    const std::string &value, exprt &e) const;

  std::string mathsat_value(const std::string &src);

  struct valuet
  {
    // map from array index to value
    using index_value_mapt = std::map<std::string, std::string>;
    index_value_mapt index_value_map;
    std::string value;
  };
};

#endif // CPROVER_SOLVERS_SMT1_SMT1_DEC_H
