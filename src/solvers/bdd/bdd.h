/*******************************************************************\

Module: Binary Decision Diagrams

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Choice between the different interface to BDD libraries.

#ifndef CPROVER_SOLVERS_BDD_BDD_H
#define CPROVER_SOLVERS_BDD_BDD_H

#ifdef HAVE_CUDD
#include "bdd_cudd.h"
#else
#include "bdd_miniBDD.h"
#endif // HAVE_CUDD

#endif // CPROVER_SOLVERS_BDD_BDD_H
