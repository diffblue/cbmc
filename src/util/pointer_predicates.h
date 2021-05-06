/*******************************************************************\

Module: Various predicates over pointers in programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Various predicates over pointers in programs

#ifndef CPROVER_UTIL_POINTER_PREDICATES_H
#define CPROVER_UTIL_POINTER_PREDICATES_H

#include "deprecate.h"
#include "std_expr.h"

#define SYMEX_DYNAMIC_PREFIX "symex_dynamic::"

exprt same_object(const exprt &p1, const exprt &p2);
exprt deallocated(const exprt &pointer, const namespacet &);
exprt dead_object(const exprt &pointer, const namespacet &);
exprt pointer_offset(const exprt &pointer);
exprt pointer_object(const exprt &pointer);
DEPRECATED(SINCE(2021, 5, 6, "Unnecessary, remove any use"))
exprt malloc_object(const exprt &pointer, const namespacet &);
exprt object_size(const exprt &pointer);
DEPRECATED(SINCE(2021, 5, 6, "Use is_dynamic_object_exprt instead"))
exprt dynamic_object(const exprt &pointer);
exprt good_pointer(const exprt &pointer);
exprt good_pointer_def(const exprt &pointer, const namespacet &);
exprt null_object(const exprt &pointer);
exprt null_pointer(const exprt &pointer);
exprt integer_address(const exprt &pointer);
exprt object_lower_bound(
  const exprt &pointer,
  const exprt &offset);
exprt object_upper_bound(
  const exprt &pointer,
  const exprt &access_size);

class is_invalid_pointer_exprt : public unary_predicate_exprt
{
public:
  explicit is_invalid_pointer_exprt(exprt pointer)
    : unary_predicate_exprt{ID_is_invalid_pointer, std::move(pointer)}
  {
  }
};

template <>
inline bool can_cast_expr<is_invalid_pointer_exprt>(const exprt &base)
{
  return base.id() == ID_is_invalid_pointer;
}

inline void validate_expr(const is_invalid_pointer_exprt &value)
{
  validate_operands(value, 1, "is_invalid_pointer must have one operand");
}

#endif // CPROVER_UTIL_POINTER_PREDICATES_H
