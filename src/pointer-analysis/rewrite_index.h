/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Dereferencing

#ifndef CPROVER_POINTER_ANALYSIS_REWRITE_INDEX_H
#define CPROVER_POINTER_ANALYSIS_REWRITE_INDEX_H

#include <util/deprecate.h>

class dereference_exprt;
class index_exprt;

// rewrite a[i] to *(a+i)
DEPRECATED(SINCE(2022, 07, 23, "implement the transform directly"))
dereference_exprt rewrite_index(const index_exprt &index_expr);

#endif // CPROVER_POINTER_ANALYSIS_REWRITE_INDEX_H
