/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SAT_ICNF_H
#define CPROVER_SOLVERS_SAT_ICNF_H

#include "satcheck_minisat2.h"

#include <fstream>

/// dumps incrementally generated propositional formulas into a
/// file in the icnf file format, documented at
/// http://www.siert.nl/icnf/
/// The tempalte parameter must be one of
/// satcheck_minisat_no_simplifiert or satcheck_minisat_simplifiert
template <class sub_solvert>
class icnft : public sub_solvert
{
public:
  icnft(message_handlert &_message_handler, const std::string &file_name)
    : sub_solvert(_message_handler), out(file_name)
  {
  }

  void lcnf(const bvt &bv) override final;
  cnft::resultt do_prop_solve() override;

protected:
  std::ofstream out;
  using sub_solvert::assumptions;
};

#endif // CPROVER_SOLVERS_SAT_ICNF_H
