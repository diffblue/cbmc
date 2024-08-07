/*******************************************************************\

Module: Writing DIMACS Files

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Writing DIMACS Files

#ifndef CPROVER_SOLVERS_FLATTENING_BV_DIMACS_H
#define CPROVER_SOLVERS_FLATTENING_BV_DIMACS_H

#include "bv_pointers.h"

class dimacs_cnft;

class bv_dimacst : public bv_pointerst
{
public:
  bv_dimacst(
    const namespacet &_ns,
    dimacs_cnft &_prop,
    message_handlert &message_handler,
    const std::string &_filename);

  virtual ~bv_dimacst()
  {
    write_dimacs();
  }

protected:
  const std::string filename;
  const dimacs_cnft &dimacs_cnf_prop;

  bool write_dimacs();
  bool write_dimacs(std::ostream &);
};

#endif // CPROVER_SOLVERS_FLATTENING_BV_DIMACS_H
