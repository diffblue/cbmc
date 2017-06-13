/*******************************************************************\

Module: Reading DIMACS CNF

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Reading DIMACS CNF

#ifndef CPROVER_SOLVERS_SAT_READ_DIMACS_CNF_H
#define CPROVER_SOLVERS_SAT_READ_DIMACS_CNF_H

#include "cnf.h"

void read_dimacs_cnf(std::istream &in, cnft &dest);

#endif // CPROVER_SOLVERS_SAT_READ_DIMACS_CNF_H
