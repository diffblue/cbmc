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

#include <optional>

class exprt;
class namespacet;
class struct_typet;
class typet;
class member_exprt;

std::optional<mp_integer> member_offset(
  const struct_typet &type,
  const irep_idt &member,
  const namespacet &ns);

std::optional<mp_integer> member_offset_bits(
  const struct_typet &type,
  const irep_idt &member,
  const namespacet &ns);

std::optional<mp_integer>
pointer_offset_size(const typet &type, const namespacet &ns);

std::optional<mp_integer>
pointer_offset_bits(const typet &type, const namespacet &ns);

/// Returns true iff \p type has effective width of zero bits.
/// In addition to the obvious \c ID_empty, this recognises
/// struct/union types whose components are all zero-width and arrays
/// of zero-width elements, mirroring the semantics that the
/// bit-blasting back-ends use to skip such types. Tag types
/// (\c ID_struct_tag, \c ID_union_tag, \c ID_c_enum_tag) are unwrapped
/// via \p ns before further recursion; \c ID_c_enum types recurse
/// into their underlying integer type.
bool is_zero_width(const typet &type, const namespacet &ns);

std::optional<mp_integer>
compute_pointer_offset(const exprt &expr, const namespacet &ns);

std::optional<exprt>
member_offset_expr(const member_exprt &, const namespacet &ns);

std::optional<exprt> member_offset_expr(
  const struct_typet &type,
  const irep_idt &member,
  const namespacet &ns);

std::optional<exprt> size_of_expr(const typet &type, const namespacet &ns);

std::optional<exprt> get_subexpression_at_offset(
  const exprt &expr,
  const mp_integer &offset,
  const typet &target_type,
  const namespacet &ns);

std::optional<exprt> get_subexpression_at_offset(
  const exprt &expr,
  const exprt &offset,
  const typet &target_type,
  const namespacet &ns);

#endif // CPROVER_UTIL_POINTER_OFFSET_SIZE_H
