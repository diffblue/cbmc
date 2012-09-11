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
//#define SATCHECK_PRECOSAT
//#define SATCHECK_PICOSAT

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

typedef satcheck_minisat1t satcheckt;

#else
#ifdef SATCHECK_MINISAT2

#include "satcheck_minisat2.h"

typedef satcheck_minisat_simplifiert satcheckt;

#else
#ifdef SATCHECK_PRECOSAT

#include "satcheck_precosat.h"

typedef satcheck_precosatt satcheckt;

#else
#ifdef SATCHECK_PICOSAT

#include "satcheck_picosat.h"

typedef satcheck_picosatt satcheckt;

#else
#error NO SAT CHECKER
#endif
#endif
#endif
#endif
#endif
#endif

#endif
