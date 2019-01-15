/*******************************************************************\

Module: Guard Data Structure

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Guard Data Structure

#ifndef CPROVER_ANALYSES_GUARD_H
#define CPROVER_ANALYSES_GUARD_H

#ifdef BDD_GUARDS

#include "guard_bdd.h"

using guard_managert = bdd_exprt;
using guardt = guard_bddt;

#else

#include "guard_expr.h"

using guard_managert = guard_expr_managert;
using guardt = guard_exprt;

#endif // BDD_GUARDS

#endif // CPROVER_ANALYSES_GUARD_H
