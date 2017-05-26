/*******************************************************************\

Module: Produce code for simple implementation of String Java libraries

Author: Romain Brenguier

Date:   March 2017

\*******************************************************************/

/// \file
/// Produce code for simple implementation of String Java libraries

#ifndef CPROVER_JAVA_BYTECODE_JAVA_STRING_LIBRARY_PREPROCESS_H
#define CPROVER_JAVA_BYTECODE_JAVA_STRING_LIBRARY_PREPROCESS_H

#include <util/ui_message.h>
#include <util/std_code.h>
#include <util/symbol_table.h>
#include <util/refined_string_type.h>
#include <util/string_expr.h>

#include <util/ieee_float.h> // should get rid of this

#include <unordered_set>
#include <functional>
#include "character_refine_preprocess.h"
#include "java_types.h"

class java_string_library_preprocesst:public messaget
{
public:
  java_string_library_preprocesst():
    refined_string_type(java_int_type(), java_char_type()) {}

  void initialize_conversion_table();
  void initialize_refined_string_type();

  exprt code_for_function(
    const irep_idt &function_id,
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  codet replace_character_call(code_function_callt call)
  {
    return character_preprocess.replace_character_call(call);
  }
  void add_string_type(const irep_idt &class_name, symbol_tablet &symbol_table);
  bool is_known_string_type(irep_idt class_name);

private:
  // We forbid copies of the object
  java_string_library_preprocesst(
    const java_string_library_preprocesst &)=delete;

  static bool java_type_matches_tag(const typet &type, const std::string &tag);
  static bool is_java_string_pointer_type(const typet &type);
  static bool is_java_string_type(const typet &type);
  static bool is_java_string_builder_type(const typet &type);
  static bool is_java_string_builder_pointer_type(const typet &type);
  static bool is_java_string_buffer_type(const typet &type);
  static bool is_java_string_buffer_pointer_type(const typet &type);
  static bool is_java_char_sequence_type(const typet &type);
  static bool is_java_char_sequence_pointer_type(const typet &type);
  static bool is_java_char_array_type(const typet &type);
  static bool is_java_char_array_pointer_type(const typet &type);
  static bool implements_java_char_sequence(const typet &type)
  {
    return
      is_java_char_sequence_pointer_type(type) ||
      is_java_string_builder_pointer_type(type) ||
      is_java_string_buffer_pointer_type(type) ||
      is_java_string_pointer_type(type);
  }

  character_refine_preprocesst character_preprocess;

  const refined_string_typet refined_string_type;

  typedef
    std::function<codet(
      const code_typet &, const source_locationt &, symbol_tablet &)>
    conversion_functiont;

  typedef std::unordered_map<irep_idt, irep_idt, irep_id_hash> id_mapt;

  // Table mapping each java method signature to the code generating function
  std::unordered_map<irep_idt, conversion_functiont, irep_id_hash>
    conversion_table;

  // Some Java functions have an equivalent in the solver that we will
  // call with the same argument and will return the same result
  id_mapt cprover_equivalent_to_java_function;

  // Some Java functions have an equivalent except that they should
  // return Java Strings instead of string_exprt
  id_mapt cprover_equivalent_to_java_string_returning_function;

  // Some Java initialization function initialize strings with the
  // same result as some function of the solver
  id_mapt cprover_equivalent_to_java_constructor;

  // Some Java functions have an equivalent in the solver except that
  // in addition they assign the result to the object on which it is called
  id_mapt cprover_equivalent_to_java_assign_and_return_function;

  // Some Java functions have an equivalent in the solver except that
  // they assign the result to the object on which it is called instead
  // of returning it
  id_mapt cprover_equivalent_to_java_assign_function;

  // A set tells us what java types should be considered as string objects
  std::unordered_set<irep_idt, irep_id_hash> string_types;

  // Conversion functions
  codet make_string_builder_append_object_code(
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  codet make_equals_function_code(
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  codet make_string_builder_append_float_code(
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  codet make_float_to_string_code(
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  codet make_string_to_char_array_code(
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  codet make_copy_string_code(
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  codet make_copy_constructor_code(
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  // Auxiliary functions
  codet code_for_scientific_notation(
    const exprt &arg,
    const ieee_float_spect &float_spec,
    const string_exprt &string_expr,
    const exprt &tmp_string,
    const refined_string_typet &refined_string_type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  // Helper functions
  exprt::operandst process_parameters(
    const code_typet::parameterst &params,
    const source_locationt &loc,
    symbol_tablet &symbol_table,
    code_blockt &init_code);

  void process_single_operand(
    exprt::operandst &processed_ops,
    const exprt &deref,
    const source_locationt &loc,
    symbol_tablet &symbol_table,
    code_blockt &init_code);

  exprt::operandst process_operands(
    const exprt::operandst &operands,
    const source_locationt &loc,
    symbol_tablet &symbol_table,
    code_blockt &init_code);

  exprt::operandst process_equals_function_operands(
    const exprt::operandst &operands,
    const source_locationt &loc,
    symbol_tablet &symbol_table,
    code_blockt &init_code);

  string_exprt replace_char_array(
    const exprt &array_pointer,
    const source_locationt &loc,
    symbol_tablet &symbol_table,
    code_blockt &code);

  void declare_function(
    irep_idt function_name, const typet &type, symbol_tablet &symbol_table);

  typet get_data_type(
    const typet &type, const symbol_tablet &symbol_table);
  typet get_length_type(
    const typet &type, const symbol_tablet &symbol_table);
  exprt get_data(const exprt &expr, const symbol_tablet &symbol_table);
  exprt get_length(const exprt &expr, const symbol_tablet &symbol_table);

  symbol_exprt fresh_string(
    const typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  symbol_exprt fresh_array(
    const typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  string_exprt fresh_string_expr(
    const source_locationt &loc,
    symbol_tablet &symbol_table,
    code_blockt &code);

  exprt fresh_string_expr_symbol(
    const source_locationt &loc,
    symbol_tablet &symbol_table,
    code_blockt &code);

  exprt allocate_fresh_string(
    const typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table,
    code_blockt &code);

  exprt allocate_fresh_array(
    const typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table,
    code_blockt &code);

  exprt make_function_application(
    const irep_idt &function_name,
    const exprt::operandst &arguments,
    const typet &type,
    symbol_tablet &symbol_table);

  codet code_assign_function_application(
    const exprt &lhs,
    const irep_idt &function_name,
    const exprt::operandst &arguments,
    symbol_tablet &symbol_table);

  codet code_return_function_application(
    const irep_idt &function_name,
    const exprt::operandst &arguments,
    const typet &type,
    symbol_tablet &symbol_table);

  codet code_assign_function_to_string_expr(
    const string_exprt &string_expr,
    const irep_idt &function_name,
    const exprt::operandst &arguments,
    symbol_tablet &symbol_table);

  string_exprt string_expr_of_function_application(
    const irep_idt &function_name,
    const exprt::operandst &arguments,
    const source_locationt &loc,
    symbol_tablet &symbol_table,
    code_blockt &code);

  codet code_assign_components_to_java_string(
    const exprt &lhs,
    const exprt &rhs_array,
    const exprt &rhs_length,
    symbol_tablet &symbol_table);

  codet code_assign_string_expr_to_java_string(
    const exprt &lhs, const string_exprt &rhs, symbol_tablet &symbol_table);

  codet code_assign_string_expr_to_new_java_string(
    const exprt &lhs,
    const string_exprt &rhs,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  codet code_assign_java_string_to_string_expr(
    const string_exprt &lhs, const exprt &rhs, symbol_tablet &symbol_table);

  codet code_assign_string_literal_to_string_expr(
    const string_exprt &lhs,
    const exprt &tmp_string,
    const std::string &s,
    symbol_tablet &symbol_table);

  exprt string_literal(const std::string &s);

  codet make_function_from_call(
    const irep_idt &function_name,
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  codet make_init_function_from_call(
    const irep_idt &function_name,
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table,
    bool ignore_first_arg=true);

  codet make_assign_and_return_function_from_call(
    const irep_idt &function_name,
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  codet make_assign_function_from_call(
    const irep_idt &function_name,
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  codet make_string_returning_function_from_call(
    const irep_idt &function_name,
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_STRING_LIBRARY_PREPROCESS_H
