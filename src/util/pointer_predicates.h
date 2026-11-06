/*******************************************************************\

Module: Various predicates over pointers in programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Various predicates over pointers in programs

#ifndef CPROVER_UTIL_POINTER_PREDICATES_H
#define CPROVER_UTIL_POINTER_PREDICATES_H

#include "std_expr.h"

#define SYMEX_DYNAMIC_PREFIX "symex_dynamic"

exprt same_object(const exprt &p1, const exprt &p2);
exprt deallocated(const exprt &pointer, const namespacet &);
exprt dead_object(const exprt &pointer, const namespacet &);
exprt pointer_offset(const exprt &pointer);
exprt pointer_object(const exprt &pointer);
exprt object_size(const exprt &pointer);
exprt null_object(const exprt &pointer);

exprt integer_address(const exprt &pointer);

/// A predicate that holds for pointers that denote an integer (e.g.
/// memory-mapped or device) address rather than a real allocated object.
/// Under the standard encoding this is equivalent to
/// `integer_address(pointer)`; the wide pointer encoding gives such pointers
/// dedicated objects and recognises them directly, which `integer_address`
/// (built on `same_object` with NULL) cannot. Used by the memory-mapped I/O
/// instrumentation.
exprt is_integer_address(const exprt &pointer);
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
