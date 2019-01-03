/*******************************************************************\

Module: Writing DIMACS Files

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Writing DIMACS Files

#ifndef CPROVER_SOLVERS_FLATTENING_BV_DIMACS_H
#define CPROVER_SOLVERS_FLATTENING_BV_DIMACS_H

#include "bv_pointers.h"

class bv_dimacst : public bv_pointerst
{
public:
  bv_dimacst(const namespacet &_ns, propt &_prop, const std::string &_filename)
    : bv_pointerst(_ns, _prop), filename(_filename)
  {
  }

  virtual ~bv_dimacst()
  {
    write_dimacs();
  }

protected:
  const std::string filename;
  bool write_dimacs();
  bool write_dimacs(std::ostream &);
};

#endif // CPROVER_SOLVERS_FLATTENING_BV_DIMACS_H
