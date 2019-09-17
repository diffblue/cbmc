/*******************************************************************\

Module: Java bytecode

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_CODE_WITH_REFERENCES_H
#define CPROVER_JAVA_BYTECODE_CODE_WITH_REFERENCES_H

#include <memory>
#include <util/std_code.h>

/// Allocate a fresh array of length \p array_length_expr and assigns \p expr
/// to it.
codet allocate_array(
  const exprt &expr,
  const exprt &array_length_expr,
  const source_locationt &loc);

/// Information to store when several references point to the same Java object.
struct object_creation_referencet
{
  /// Expression for the symbol that stores the value that may be reference
  /// equal to other values.
  exprt expr;

  /// If `symbol` is an array, this expression stores its length.
  /// This should only be set once the actual elements of the array have been
  /// seen, not the first time an `@ref` have been seen, only when `@id` is
  /// seen.
  optionalt<exprt> array_length;
};

#endif // CPROVER_JAVA_BYTECODE_CODE_WITH_REFERENCES_H
