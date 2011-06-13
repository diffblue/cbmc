/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SATCHECK_H
#define CPROVER_SATCHECK_H

// this picks the "default" SAT solver

//#define SATCHECK_ZCHAFF
//#define SATCHECK_MINISAT1
#define SATCHECK_MINISAT2
//#define SATCHECK_BOOLEFORCE

#ifdef SATCHECK_ZCHAFF

#include "satcheck_zchaff.h"

typedef satcheck_zchafft satcheckt;

#else
#ifdef SATCHECK_BOOLEFORCE

#include "satcheck_booleforce.h"

typedef satcheck_booleforcet satcheckt;

#else

#ifdef SATCHECK_MINISAT1

#include "satcheck_minisat.h"

typedef satcheck_minisatt satcheckt;

#else
#ifdef SATCHECK_MINISAT2

#include "satcheck_minisat2.h"

typedef satcheck_minisat_coret satcheckt;

#else
#error NO SAT CHECKER
#endif
#endif
#endif
#endif

#endif
