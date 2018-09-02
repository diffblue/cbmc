/*******************************************************************\

Module: Writing DIMACS Files

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Writing DIMACS Files

#ifndef CPROVER_CBMC_CBMC_DIMACS_H
#define CPROVER_CBMC_CBMC_DIMACS_H

#include <solvers/flattening/bv_pointers.h>

class cbmc_dimacst : public bv_pointerst
{
public:
  cbmc_dimacst(
    const namespacet &_ns,
    propt &_prop,
    const std::string &_filename)
    : bv_pointerst(_ns, _prop), filename(_filename)
  {
  }

  virtual ~cbmc_dimacst()
  {
    write_dimacs(filename);
  }

protected:
  std::string filename;
  bool write_dimacs(const std::string &filename);
  bool write_dimacs(std::ostream &);
};

#endif // CPROVER_CBMC_CBMC_DIMACS_H
