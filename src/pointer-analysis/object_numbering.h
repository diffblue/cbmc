/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_OBJECT_NUMBERING_H
#define CPROVER_POINTER_ANALYSIS_OBJECT_NUMBERING_H

#include <util/hash_cont.h>
#include <util/expr.h>
#include <util/numbering.h>

typedef hash_numbering<exprt, irep_hash> object_numberingt;

#endif
