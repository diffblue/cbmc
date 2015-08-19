/*******************************************************************\

Module: Writing DIMACS Files

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_DIMACS_H
#define CPROVER_CBMC_DIMACS_H

#include "bv_cbmc.h"

class cbmc_dimacst:public bv_cbmct
{
public:
  cbmc_dimacst(
    const namespacet &_ns,
    propt &_prop):bv_cbmct(_ns, _prop) { }
  virtual ~cbmc_dimacst() { }

  bool write_dimacs(const std::string &filename);
  bool write_dimacs(std::ostream &out);
};

#endif
