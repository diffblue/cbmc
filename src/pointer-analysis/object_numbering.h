/*******************************************************************\

Module: Object Numbering

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Object Numbering
///
/// This is used to abbreviate identical expressions by number: for example,
/// an object_numberingt instance might maintain the map:
/// ```
/// 1 -> constant_exprt("Hello", string_typet())
/// 2 -> constant_exprt("World", string_typet())
/// ```
/// Then any users that agree to use the same object_numberingt instance as a
/// common reference source can use '1' and '2' as shorthands for "Hello" and
/// "World" respectively.

#ifndef CPROVER_POINTER_ANALYSIS_OBJECT_NUMBERING_H
#define CPROVER_POINTER_ANALYSIS_OBJECT_NUMBERING_H

#include <util/expr.h>
#include <util/numbering.h>

typedef hash_numbering<exprt, irep_hash> object_numberingt;

#endif // CPROVER_POINTER_ANALYSIS_OBJECT_NUMBERING_H
