/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SATCHECK_CORE_H
#define CPROVER_SATCHECK_CORE_H

//#define SATCHECK_CORE_ZCHAFF
//#define SATCHECK_CORE_MINISAT1
//#define SATCHECK_CORE_BOOLEFORCE

#ifdef SATCHECK_CORE_ZCHAFF

#include "satcheck_zcore.h"

typedef satcheck_zcoret satcheck_coret;

#else
#ifdef SATCHECK_CORE_BOOLEFORCE

#include "satcheck_booleforce.h"

typedef satcheck_booleforce_coret satcheck_coret;

#else

#ifdef SATCHECK_CORE_MINISAT1

#include "satcheck_minisat.h"

typedef satcheck_minisat_coret satcheck_coret;

#else
#error NO SAT CHECKER WITH CORE EXTRACTOR
#endif
#endif
#endif

#endif
