/********************************************************************\

Module: Type for string expressions used by the string solver.
        These string expressions contain a field `length`, of type
        `index_type`, a field `content` of type `content_type`.
        This module also defines functions to recognise the C and java
        string types.

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_REFINEMENT_REFINED_STRING_TYPE_H
#define CPROVER_SOLVERS_REFINEMENT_REFINED_STRING_TYPE_H

#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <ansi-c/c_types.h>
#include <java_bytecode/java_types.h>

// Internal type used for string refinement
class refined_string_typet: public struct_typet
{
public:
  explicit refined_string_typet(typet char_type);

  // Type for the content (list of characters) of a string
  const array_typet &get_content_type() const
  {
    assert(components().size()==2);
    return to_array_type(components()[1].type());
  }

  const typet &get_char_type()
  {
    assert(components().size()==2);
    return components()[0].type();
  }

  const typet &get_index_type() const
  {
    return get_content_type().size().type();
  }

  static typet index_type()
  {
    return signed_int_type();
  }

  static typet java_index_type()
  {
    return java_int_type();
  }

  // For C the unrefined string type is __CPROVER_string, for java it is a
  // pointer to a struct with tag java.lang.String

  static bool is_c_string_type(const typet &type);

  static bool is_java_string_pointer_type(const typet &type);

  static bool is_java_string_type(const typet &type);

  static bool is_java_string_builder_type(const typet &type);

  static bool is_java_char_sequence_type(const typet &type);

  static typet get_char_type(const exprt &expr)
  {
    if(is_c_string_type(expr.type()))
      return char_type();
    else
      return java_char_type();
  }

  static typet get_index_type(const exprt &expr)
  {
    if(is_c_string_type(expr.type()))
      return index_type();
    else
      return java_index_type();
  }

  static bool is_unrefined_string_type(const typet &type)
  {
    return (
      is_c_string_type(type) ||
      is_java_string_pointer_type(type) ||
      is_java_string_builder_type(type) ||
      is_java_char_sequence_type(type));
  }

  static bool is_unrefined_string(const exprt &expr)
  {
    return (is_unrefined_string_type(expr.type()));
  }

  constant_exprt index_of_int(int i) const
  {
    return from_integer(i, get_index_type());
  }
};

const refined_string_typet &to_refined_string_type(const typet &type)
{
  assert(type.id()==ID_struct);
  return static_cast<const refined_string_typet &>(type);
}

#endif
