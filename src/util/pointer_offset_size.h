/*******************************************************************\

Module: Pointer Logic

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Logic

#ifndef CPROVER_UTIL_POINTER_OFFSET_SIZE_H
#define CPROVER_UTIL_POINTER_OFFSET_SIZE_H

#include "irep.h"
#include "mp_arith.h"
#include "optional.h"

class exprt;
class namespacet;
class struct_typet;
class typet;
class member_exprt;
class constant_exprt;

// these return 'nullopt' on failure

// NOLINTNEXTLINE(readability/identifiers)
class member_offset_iterator
{
  typedef std::pair<size_t, mp_integer> refst;
  refst current;
  const struct_typet &type;
  const namespacet &ns;
  size_t bit_field_bits;
public:
  member_offset_iterator(const struct_typet &_type,
                         const namespacet &_ns);
  member_offset_iterator &operator++();
  const refst &operator*() const { return current; }
  const refst* operator->() const { return &current; }
};

optionalt<mp_integer> member_offset(
  const struct_typet &type,
  const irep_idt &member,
  const namespacet &ns);

optionalt<mp_integer> member_offset_bits(
  const struct_typet &type,
  const irep_idt &member,
  const namespacet &ns);

optionalt<mp_integer>
pointer_offset_size(const typet &type, const namespacet &ns);

optionalt<mp_integer>
pointer_offset_bits(const typet &type, const namespacet &ns);

optionalt<mp_integer>
compute_pointer_offset(const exprt &expr, const namespacet &ns);

// these return 'nil' on failure

exprt member_offset_expr(
  const member_exprt &,
  const namespacet &ns);

exprt member_offset_expr(
  const struct_typet &type,
  const irep_idt &member,
  const namespacet &ns);

exprt size_of_expr(
  const typet &type,
  const namespacet &ns);

exprt build_sizeof_expr(
  const constant_exprt &expr,
  const namespacet &ns);

exprt get_subexpression_at_offset(
  const exprt &expr,
  const mp_integer &offset,
  const typet &target_type,
  const namespacet &ns);

exprt get_subexpression_at_offset(
  const exprt &expr,
  const exprt &offset,
  const typet &target_type,
  const namespacet &ns);

#endif // CPROVER_UTIL_POINTER_OFFSET_SIZE_H
