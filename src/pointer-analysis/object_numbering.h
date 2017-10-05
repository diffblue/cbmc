/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set

#ifndef CPROVER_POINTER_ANALYSIS_OBJECT_NUMBERING_H
#define CPROVER_POINTER_ANALYSIS_OBJECT_NUMBERING_H

#include <util/expr.h>
#include <util/numbering.h>

using object_numberingt = hash_numbering<exprt, irep_hash>;

#endif // CPROVER_POINTER_ANALYSIS_OBJECT_NUMBERING_H
