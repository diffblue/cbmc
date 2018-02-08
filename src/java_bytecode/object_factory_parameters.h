/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_OBJECT_FACTORY_PARAMETERS_H
#define CPROVER_JAVA_BYTECODE_OBJECT_FACTORY_PARAMETERS_H

#include <cstdint>
#include <limits>

#define MAX_NONDET_ARRAY_LENGTH_DEFAULT 5
#define MAX_NONDET_STRING_LENGTH std::numeric_limits<std::int32_t>::max()
#define MAX_NONDET_TREE_DEPTH 5

struct object_factory_parameterst final
{
  /// Maximum value for the non-deterministically-chosen length of an array.
  size_t max_nondet_array_length=MAX_NONDET_ARRAY_LENGTH_DEFAULT;

  /// Maximum value for the non-deterministically-chosen length of a string.
  size_t max_nondet_string_length=MAX_NONDET_STRING_LENGTH;

  /// Maximum depth for object hierarchy on input.
  /// Used to prevent object factory to loop infinitely during the
  /// generation of code that allocates/initializes data structures of recursive
  /// data types or unbounded depth. We bound the maximum number of times we
  /// dereference a pointer using a 'depth counter'. We set a pointer to null if
  /// such depth becomes >= than this maximum value.
  size_t max_nondet_tree_depth=MAX_NONDET_TREE_DEPTH;

  /// Force string content to be ASCII printable characters when set to true.
  bool string_printable = false;
};

#endif
