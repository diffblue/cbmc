// Author: Diffblue Ltd.

#include "object_tracking.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/prefix.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/string_constant.h>

exprt make_invalid_pointer_expr()
{
  return constant_exprt(ID_invalid, pointer_type(void_type()));
}

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
  null_object.size = from_integer(0, size_type());
  null_object.is_dynamic = false;
  return null_object;
}

static decision_procedure_objectt make_invalid_pointer_object()
{
  decision_procedure_objectt invalid_pointer_object;
  // Using unique_id = 1, so 0 is the NULL object, 1 is the invalid object and
  // other valid objects have unique_id > 1.
  invalid_pointer_object.unique_id = 1;
  invalid_pointer_object.base_expression = make_invalid_pointer_expr();
  invalid_pointer_object.size = from_integer(0, size_type());
  invalid_pointer_object.is_dynamic = false;
  return invalid_pointer_object;
}

smt_object_mapt initial_smt_object_map()
{
  smt_object_mapt object_map;
  decision_procedure_objectt null_object = make_null_object();
  exprt null_object_base = null_object.base_expression;
  object_map.emplace(std::move(null_object_base), std::move(null_object));
  decision_procedure_objectt invalid_pointer_object =
    make_invalid_pointer_object();
  exprt invalid_pointer_object_base = invalid_pointer_object.base_expression;
  object_map.emplace(
    std::move(invalid_pointer_object_base), std::move(invalid_pointer_object));
  return object_map;
}

/// This function returns true for heap allocated objects or false for stack
/// allocated objects.
static bool is_dynamic(const exprt &object)
{
  // This check corresponds to the symbols created in
  // `goto_symext::symex_allocate`, which implements the `__CPROVER_allocate`
  // intrinsic function used by the standard library models.
  const bool dynamic_type = object.type().get_bool(ID_C_dynamic);
  if(dynamic_type)
    return true;
  const auto symbol = expr_try_dynamic_cast<symbol_exprt>(object);
  bool symbol_is_dynamic =
    symbol &&
    has_prefix(id2string(symbol->get_identifier()), SYMEX_DYNAMIC_PREFIX);
  return symbol_is_dynamic;
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
      const auto size = size_of_expr(object_base.type(), ns);
      INVARIANT(size, "Objects are expected to have well defined size");
      decision_procedure_objectt object;
      object.base_expression = object_base;
      object.unique_id = object_map.size();
      object.size = *size;
      object.is_dynamic = is_dynamic(object_base);
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
