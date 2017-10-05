/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_SATCHECK_CORE_H
#define CPROVER_SOLVERS_SAT_SATCHECK_CORE_H

// #define SATCHECK_CORE_ZCHAFF
// #define SATCHECK_CORE_MINISAT1
// #define SATCHECK_CORE_BOOLEFORCE

#ifdef SATCHECK_CORE_ZCHAFF

#include "satcheck_zcore.h"

using satcheck_coret = satcheck_zcoret;

#else
#ifdef SATCHECK_CORE_BOOLEFORCE

#include "satcheck_booleforce.h"

using satcheck_coret = satcheck_booleforce_coret;

#else

#ifdef SATCHECK_CORE_MINISAT1

#include "satcheck_minisat.h"

using satcheck_coret = satcheck_minisat1_coret;

#else
#error NO SAT CHECKER WITH CORE EXTRACTOR
#endif
#endif
#endif

#endif // CPROVER_SOLVERS_SAT_SATCHECK_CORE_H
