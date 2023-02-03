/*******************************************************************\

Module: Flatten OK Expressions

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "flatten_ok_expr.h"

#include <util/c_types.h>

#include "state.h"

exprt flatten(const state_ok_exprt &ok_expr)
{
  const auto &state = ok_expr.state();
  const auto &pointer = ok_expr.address();
  const auto &size = ok_expr.size();

  // X_ok(p, s) <-->
  //   live_object(p)
  // ∧ offset(p)+s≤object_size(p)
  // ∧ writeable_object(p)           if applicable

  auto live_object = state_live_object_exprt(state, pointer);

  auto writeable_object = state_writeable_object_exprt(state, pointer);

  auto ssize_type = signed_size_type();
  auto offset = pointer_offset_exprt(pointer, ssize_type);

  auto size_type = ::size_type();

  // extend one bit, to cover overflow case
  auto size_type_ext = unsignedbv_typet(size_type.get_width() + 1);

  auto object_size = state_object_size_exprt(state, pointer, size_type);

  auto object_size_casted = typecast_exprt(object_size, size_type_ext);

  auto offset_casted_to_unsigned =
    typecast_exprt::conditional_cast(offset, size_type);
  auto offset_extended =
    typecast_exprt::conditional_cast(offset_casted_to_unsigned, size_type_ext);
  auto size_casted = typecast_exprt::conditional_cast(size, size_type_ext);
  auto upper = binary_relation_exprt(
    plus_exprt(offset_extended, size_casted), ID_le, object_size_casted);

  auto conjunction = and_exprt(live_object, upper);

  if(ok_expr.id() == ID_state_w_ok || ok_expr.id() == ID_state_rw_ok)
    conjunction.add_to_operands(std::move(writeable_object));

  return std::move(conjunction);
}
