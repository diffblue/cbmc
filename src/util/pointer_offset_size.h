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

optionalt<exprt> member_offset_expr(const member_exprt &, const namespacet &ns);

optionalt<exprt> member_offset_expr(
  const struct_typet &type,
  const irep_idt &member,
  const namespacet &ns);

optionalt<exprt> size_of_expr(const typet &type, const namespacet &ns);

optionalt<exprt> get_subexpression_at_offset(
  const exprt &expr,
  const mp_integer &offset,
  const typet &target_type,
  const namespacet &ns);

optionalt<exprt> get_subexpression_at_offset(
  const exprt &expr,
  const exprt &offset,
  const typet &target_type,
  const namespacet &ns);

#endif // CPROVER_UTIL_POINTER_OFFSET_SIZE_H
