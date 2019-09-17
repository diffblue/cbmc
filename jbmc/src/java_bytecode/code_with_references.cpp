/*******************************************************************\

Module: Java bytecode

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include "code_with_references.h"
#include "java_types.h"
#include <util/arith_tools.h>

codet allocate_array(
  const exprt &expr,
  const exprt &array_length_expr,
  const source_locationt &loc)
{
  const pointer_typet &pointer_type = to_pointer_type(expr.type());
  const auto &element_type =
    java_array_element_type(to_struct_tag_type(pointer_type.subtype()));
  side_effect_exprt java_new_array{ID_java_new_array, pointer_type};
  java_new_array.copy_to_operands(array_length_expr);
  java_new_array.type().subtype().set(ID_element_type, element_type);
  return code_assignt{expr, java_new_array, loc};
}
