/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_DIMACS_H
#define CPROVER_CBMC_DIMACS_H

#include "bv_cbmc.h"

class dimacst:public bv_cbmct
{
public:
  dimacst(
    const namespacet &_ns,
    propt &_prop):bv_cbmct(_ns, _prop) { }
  virtual ~dimacst() { }

  bool write_dimacs(const std::string &filename);
  bool write_dimacs(std::ostream &out);

};

#endif
