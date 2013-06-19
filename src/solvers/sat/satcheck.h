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
//#define SATCHECK_GLUCOSE
//#define SATCHECK_BOOLEFORCE
//#define SATCHECK_PRECOSAT
//#define SATCHECK_PICOSAT
//#define SATCHECK_LINGELING

#if defined SATCHECK_ZCHAFF

#include "satcheck_zchaff.h"

typedef satcheck_zchafft satcheckt;

#elif defined SATCHECK_BOOLEFORCE

#include "satcheck_booleforce.h"

typedef satcheck_booleforcet satcheckt;

#elif defined SATCHECK_MINISAT1

#include "satcheck_minisat.h"

typedef satcheck_minisat1t satcheckt;

#elif defined SATCHECK_MINISAT2

#include "satcheck_minisat2.h"

typedef satcheck_minisat_simplifiert satcheckt;

#elif defined SATCHECK_PRECOSAT

#include "satcheck_precosat.h"

typedef satcheck_precosatt satcheckt;

#elif defined SATCHECK_PICOSAT

#include "satcheck_picosat.h"

typedef satcheck_picosatt satcheckt;

#elif defined SATCHECK_LINGELING

#include "satcheck_lingeling.h"

typedef satcheck_lingelingt satcheckt;

#elif defined SATCHECK_GLUCOSE

#include "satcheck_glucose.h"

typedef satcheck_glucose_simplifiert satcheckt;

#endif

#endif
