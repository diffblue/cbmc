/*******************************************************************\

Module: Java bytecode

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include "code_with_references.h"
#include "java_types.h"

#include <goto-programs/goto_instruction_code.h>

#include <util/arith_tools.h>

codet allocate_array(
  const exprt &expr,
  const exprt &array_length_expr,
  const source_locationt &loc)
{
  pointer_typet pointer_type = to_pointer_type(expr.type());
  const auto &element_type =
    java_array_element_type(to_struct_tag_type(pointer_type.base_type()));
  pointer_type.base_type().set(ID_element_type, element_type);
  side_effect_exprt java_new_array{
    ID_java_new_array, {array_length_expr}, pointer_type, loc};
  return code_frontend_assignt{expr, java_new_array, loc};
}

code_blockt
reference_allocationt::to_code(reference_substitutiont &references) const
{
  const object_creation_referencet &reference = references(reference_id);
  INVARIANT(reference.array_length, "Length of reference array must be known");
  if(can_cast_expr<constant_exprt>(*reference.array_length))
  {
    return code_blockt(
      {allocate_array(reference.expr, *reference.array_length, loc)});
  }
  // Fallback in case the array definition has not been seen yet, this can
  // happen if `to_code` is called before the whole json file has been processed
  // or the "@id" json field corresponding to `reference_id` doesn't appear in
  // the file.
  code_blockt code;
  code.add(code_frontend_assignt{
    *reference.array_length, side_effect_expr_nondett{java_int_type(), loc}});
  code.add(code_assumet{binary_predicate_exprt{
    *reference.array_length, ID_ge, from_integer(0, java_int_type())}});
  code.add(allocate_array(reference.expr, *reference.array_length, loc));
  return code;
}

void code_with_references_listt::add(code_without_referencest code)
{
  auto ptr = std::make_shared<code_without_referencest>(std::move(code));
  list.emplace_back(std::move(ptr));
}

void code_with_references_listt::add(codet code)
{
  add(code_without_referencest{std::move(code)});
}

void code_with_references_listt::add(reference_allocationt ref)
{
  auto ptr = std::make_shared<reference_allocationt>(std::move(ref));
  list.emplace_back(std::move(ptr));
}

void code_with_references_listt::append(code_with_references_listt &&other)
{
  list.splice(list.end(), other.list);
}

void code_with_references_listt::add_to_front(code_without_referencest code)
{
  auto ptr = std::make_shared<code_without_referencest>(std::move(code));
  list.emplace_front(std::move(ptr));
}
