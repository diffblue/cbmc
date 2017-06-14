/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SMT2_SMT2IREP_H
#define CPROVER_SOLVERS_SMT2_SMT2IREP_H

#include <iosfwd>

#include <util/irep.h>

irept smt2irep(std::istream &);

#endif // CPROVER_SOLVERS_SMT2_SMT2IREP_H
