/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "satcheck.h"

// Sanity check

#ifdef SATCHECK_MINISAT1
#ifndef HAVE_MINISAT
#error "I expected to have MiniSat 1"
#endif
#endif

#ifdef SATCHECK_MINISAT2
#ifndef HAVE_MINISAT2
#error "I expected to have MiniSat 2"
#endif
#endif
