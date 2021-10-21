/*******************************************************************\

Module: Implementation of CProver.createArrayWithType intrinsic

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Implementation of CProver.createArrayWithType intrinsic

#include "create_array_with_type_intrinsic.h"

#include <java_bytecode/java_types.h>

#include <util/fresh_symbol.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/symbol_table_base.h>

/// Returns the symbol name for `org.cprover.CProver.createArrayWithType`
irep_idt get_create_array_with_type_name()
{
  static irep_idt create_array_with_type_name =
    "java::org.cprover.CProver.createArrayWithType:"
    "(I[Ljava/lang/Object;)[Ljava/lang/Object;";
  return create_array_with_type_name;
}

/// Returns the internal implementation for
/// `org.cprover.CProver.createArrayWithType`. Our implementation copies the
/// internal type information maintained by jbmc that tracks the runtime type
/// of an array object rather than using reflection to achieve similar type
/// cloning.
/// \param function_id: identifier of the function being produced. Currently
///   always `get_create_array_with_type_name()`
/// \param symbol_table: global symbol table
/// \param message_handler: any GOTO program conversion errors are logged here
/// \return new GOTO program body for `org.cprover.CProver.createArrayWithType`.
codet create_array_with_type_body(
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  // Replace CProver.createArrayWithType, which uses reflection to copy the
  // type but not the content of a given array, with a java_new_array statement
  // followed by overwriting its element type and dimension, similar to our
  // implementation (in java_bytecode_convert_class.cpp) of the
  // array[reference].clone() method.

  PRECONDITION(function_id == get_create_array_with_type_name());

  namespacet ns{symbol_table};

  const symbolt &function_symbol =
    symbol_table.lookup_ref(get_create_array_with_type_name());
  const auto &function_type = to_code_type(function_symbol.type);
  const auto &length_argument = function_type.parameters().at(0);
  symbol_exprt length_argument_symbol_expr{length_argument.get_identifier(),
                                           length_argument.type()};
  const auto &existing_array_argument = function_type.parameters().at(1);
  symbol_exprt existing_array_argument_symbol_expr{
    existing_array_argument.get_identifier(), existing_array_argument.type()};

  symbolt &new_array_symbol = get_fresh_aux_symbol(
    function_type.parameters().at(1).type(),
    id2string(get_create_array_with_type_name()),
    "new_array",
    source_locationt(),
    ID_java,
    symbol_table);
  const auto new_array_symbol_expr = new_array_symbol.symbol_expr();

  code_blockt code_block;

  // Declare new_array temporary:
  code_block.add(code_frontend_declt(new_array_symbol_expr));

  // new_array = new Object[length];
  side_effect_exprt new_array_expr{
    ID_java_new_array, new_array_symbol.type, source_locationt{}};
  new_array_expr.copy_to_operands(length_argument_symbol_expr);
  code_block.add(code_frontend_assignt(new_array_symbol_expr, new_array_expr));

  dereference_exprt existing_array(existing_array_argument_symbol_expr);
  dereference_exprt new_array(new_array_symbol_expr);

  // new_array.@array_dimensions = existing_array.@array_dimensions
  // new_array.@element_class_identifier =
  //   existing_array.@element_class_identifier
  member_exprt old_array_dimension(
    existing_array, JAVA_ARRAY_DIMENSION_FIELD_NAME, java_int_type());
  member_exprt old_array_element_classid(
    existing_array, JAVA_ARRAY_ELEMENT_CLASSID_FIELD_NAME, string_typet());

  member_exprt new_array_dimension(
    new_array, JAVA_ARRAY_DIMENSION_FIELD_NAME, java_int_type());
  member_exprt new_array_element_classid(
    new_array, JAVA_ARRAY_ELEMENT_CLASSID_FIELD_NAME, string_typet());

  code_block.add(
    code_frontend_assignt(new_array_dimension, old_array_dimension));
  code_block.add(code_frontend_assignt(
    new_array_element_classid, old_array_element_classid));

  // return new_array
  code_block.add(code_frontend_returnt(new_array_symbol_expr));

  return std::move(code_block);
}
