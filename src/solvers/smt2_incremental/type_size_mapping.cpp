// Author: Diffblue Ltd.

#include "type_size_mapping.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/invariant.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>

#include <solvers/smt2_incremental/convert_expr_to_smt.h>

void associate_pointer_sizes(
  const exprt &expression,
  const namespacet &ns,
  type_size_mapt &type_size_map,
  const smt_object_mapt &object_map,
  const smt_object_sizet::make_applicationt &object_size)
{
  expression.visit_pre([&](const exprt &sub_expression) {
    if(
      const auto &pointer_type =
        type_try_dynamic_cast<pointer_typet>(sub_expression.type()))
    {
      const auto find_result = type_size_map.find(pointer_type->base_type());
      if(find_result != type_size_map.cend())
        return;
      exprt pointer_size_expr;
      // There's a special case for a pointer subtype here: the case where the
      // pointer is `void *`. This means that we don't know the underlying base
      // type, so we're just assigning a size expression value of 1 (given that
      // this is going to be used in a multiplication and 1 is the identity
      // value for multiplication)
      if(is_void_pointer(*pointer_type))
      {
        pointer_size_expr = from_integer(1, size_type());
      }
      else
      {
        auto pointer_size_opt = size_of_expr(pointer_type->base_type(), ns);
        PRECONDITION(pointer_size_opt.has_value());
        pointer_size_expr = pointer_size_opt.value();
      }
      auto pointer_size_term = convert_expr_to_smt(
        pointer_size_expr, object_map, type_size_map, object_size);
      type_size_map.emplace_hint(
        find_result, pointer_type->base_type(), pointer_size_term);
    }
  });
}
