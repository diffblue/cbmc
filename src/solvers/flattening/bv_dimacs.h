/*******************************************************************\

Module: Writing DIMACS Files

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Writing DIMACS Files

#ifndef CPROVER_SOLVERS_FLATTENING_BV_DIMACS_H
#define CPROVER_SOLVERS_FLATTENING_BV_DIMACS_H

#include <util/exit_codes.h>

#include "bv_pointers.h"

#include <cstdlib>

class bv_dimacst : public bv_pointerst
{
public:
  bv_dimacst(
    const namespacet &_ns,
    propt &_prop,
    message_handlert &message_handler,
    const std::string &_filename)
    : bv_pointerst(_ns, _prop, message_handler), filename(_filename)
  {
  }

  virtual ~bv_dimacst()
  {
    if(write_dimacs())
      exit(CPROVER_EXIT_USAGE_ERROR);
  }

protected:
  const std::string filename;
  bool write_dimacs();
  bool write_dimacs(std::ostream &);
};

#endif // CPROVER_SOLVERS_FLATTENING_BV_DIMACS_H
