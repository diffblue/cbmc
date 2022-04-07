// Author: Diffblue Ltd.

#include "object_tracking.h"

#include <util/c_types.h>
#include <util/pointer_offset_size.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/string_constant.h>

exprt find_object_base_expression(const address_of_exprt &address_of)
{
  auto current = std::ref(address_of.object());
  while(
    !(can_cast_expr<symbol_exprt>(current) ||
      can_cast_expr<constant_exprt>(current) ||
      can_cast_expr<string_constantt>(current) ||
      can_cast_expr<code_labelt>(current)))
  {
    if(const auto index = expr_try_dynamic_cast<index_exprt>(current.get()))
    {
      // For the case `my_array[bar]` the base expression is `my_array`.
      current = index->array();
      continue;
    }
    if(const auto member = expr_try_dynamic_cast<member_exprt>(current.get()))
    {
      // For the case `my_struct.field_name` the base expression is `my_struct`.
      current = member->compound();
      continue;
    }
    INVARIANT(
      false,
      "Unable to find base object of expression: " +
        current.get().pretty(1, 0));
  }
  return current.get();
}

static decision_procedure_objectt make_null_object()
{
  decision_procedure_objectt null_object;
  null_object.unique_id = 0;
  null_object.base_expression = null_pointer_exprt{pointer_type(void_type())};
  return null_object;
}

smt_object_mapt initial_smt_object_map()
{
  smt_object_mapt object_map;
  decision_procedure_objectt null_object = make_null_object();
  exprt base = null_object.base_expression;
  object_map.emplace(std::move(base), std::move(null_object));
  return object_map;
}

void track_expression_objects(
  const exprt &expression,
  const namespacet &ns,
  smt_object_mapt &object_map)
{
  find_object_base_expressions(
    expression, [&](const exprt &object_base) -> void {
      const auto find_result = object_map.find(object_base);
      if(find_result != object_map.cend())
        return;
      decision_procedure_objectt object;
      object.base_expression = object_base;
      object.unique_id = object_map.size();
      object.size = size_of_expr(object_base.type(), ns);
      object_map.emplace_hint(find_result, object_base, std::move(object));
    });
}

bool objects_are_already_tracked(
  const exprt &expression,
  const smt_object_mapt &object_map)
{
  bool all_objects_tracked = true;
  find_object_base_expressions(
    expression, [&](const exprt &object_base) -> void {
      const auto find_result = object_map.find(object_base);
      if(find_result != object_map.cend())
        return;
      all_objects_tracked = false;
    });
  return all_objects_tracked;
}
