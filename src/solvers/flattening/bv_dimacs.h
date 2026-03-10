/*******************************************************************\

Module: Writing DIMACS Files

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Writing DIMACS Files

#ifndef CPROVER_SOLVERS_FLATTENING_BV_DIMACS_H
#define CPROVER_SOLVERS_FLATTENING_BV_DIMACS_H

#include "bv_pointers.h"

#include <iosfwd>

class dimacs_cnft;

class bv_dimacst : public bv_pointerst
{
public:
  bv_dimacst(
    const namespacet &_ns,
    dimacs_cnft &_prop,
    message_handlert &message_handler,
    std::ostream &_out);

  virtual ~bv_dimacst()
  {
    write_dimacs();
  }

protected:
  std::ostream &out;
  const dimacs_cnft &dimacs_cnf_prop;

  void write_dimacs();
};

#endif // CPROVER_SOLVERS_FLATTENING_BV_DIMACS_H
