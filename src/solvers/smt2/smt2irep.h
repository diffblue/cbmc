/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVER_SMT2IREP_H
#define CPROVER_SOLVER_SMT2IREP_H

#include <iosfwd>

#include <util/irep.h>

irept smt2irep(std::istream &);

#endif
