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

#include <array>
#include <unordered_set>
#include <functional>
#include "character_refine_preprocess.h"
#include "java_types.h"

// Arbitrary limit of 10 arguments for the number of arguments to String.format
#define MAX_FORMAT_ARGS 10

class java_string_library_preprocesst:public messaget
{
public:
  java_string_library_preprocesst()
    : char_type(java_char_type()),
      index_type(java_int_type()),
      refined_string_type(index_type, char_type)
  {
  }

  void initialize_known_type_table();
  void initialize_conversion_table();
  void initialize_refined_string_type();

  bool implements_function(const irep_idt &function_id) const;
  void get_all_function_names(std::unordered_set<irep_idt> &methods) const;

  exprt
  code_for_function(const symbolt &symbol, symbol_table_baset &symbol_table);

  codet replace_character_call(code_function_callt call)
  {
    return character_preprocess.replace_character_call(call);
  }
  std::vector<irep_idt> get_string_type_base_classes(
    const irep_idt &class_name);
  void add_string_type(const irep_idt &class_name, symbol_tablet &symbol_table);
  bool is_known_string_type(irep_idt class_name);

  static bool implements_java_char_sequence_pointer(const typet &type)
  {
    return is_java_char_sequence_pointer_type(type)
           || is_java_string_builder_pointer_type(type)
           || is_java_string_buffer_pointer_type(type)
           || is_java_string_pointer_type(type);
  }
  static bool implements_java_char_sequence(const typet &type)
  {
    return is_java_char_sequence_type(type)
           || is_java_string_builder_type(type)
           || is_java_string_buffer_type(type)
           || is_java_string_type(type);
  }

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

  character_refine_preprocesst character_preprocess;

  const typet char_type;
  const typet index_type;
  const refined_string_typet refined_string_type;

  typedef std::function<codet(
    const java_method_typet &,
    const source_locationt &,
    const irep_idt &,
    symbol_table_baset &)>
    conversion_functiont;

  typedef std::unordered_map<irep_idt, irep_idt> id_mapt;

  // Table mapping each java method signature to the code generating function
  std::unordered_map<irep_idt, conversion_functiont> conversion_table;

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

  const std::array<id_mapt *, 5> id_maps = std::array<id_mapt *, 5>
    {
      {
        &cprover_equivalent_to_java_function,
        &cprover_equivalent_to_java_string_returning_function,
        &cprover_equivalent_to_java_constructor,
        &cprover_equivalent_to_java_assign_and_return_function,
        &cprover_equivalent_to_java_assign_function,
      }
    };

  // A set tells us what java types should be considered as string objects
  std::unordered_set<irep_idt> string_types;

  codet make_float_to_string_code(
    const java_method_typet &type,
    const source_locationt &loc,
    const irep_idt &function_id,
    symbol_table_baset &symbol_table);

  codet make_string_to_char_array_code(
    const java_method_typet &type,
    const source_locationt &loc,
    const irep_idt &function_id,
    symbol_tablet &symbol_table);

  codet make_string_format_code(
    const java_method_typet &type,
    const source_locationt &loc,
    const irep_idt &function_id,
    symbol_table_baset &symbol_table);

  codet make_copy_string_code(
    const java_method_typet &type,
    const source_locationt &loc,
    const irep_idt &function_id,
    symbol_table_baset &symbol_table);

  codet make_copy_constructor_code(
    const java_method_typet &type,
    const source_locationt &loc,
    const irep_idt &function_id,
    symbol_table_baset &symbol_table);

  codet make_string_length_code(
    const java_method_typet &type,
    const source_locationt &loc,
    const irep_idt &function_id,
    symbol_table_baset &symbol_table);

  codet make_object_get_class_code(
    const java_method_typet &type,
    const source_locationt &loc,
    const irep_idt &function_id,
    symbol_table_baset &symbol_table);

  // Helper functions
  exprt::operandst process_parameters(
    const java_method_typet::parameterst &params,
    const source_locationt &loc,
    symbol_table_baset &symbol_table,
    code_blockt &init_code);

  // Friending this function for unit testing convert_exprt_to_string_exprt
  friend refined_string_exprt convert_exprt_to_string_exprt_unit_test(
    java_string_library_preprocesst &preprocess,
    const exprt &deref,
    const source_locationt &loc,
    symbol_tablet &symbol_table,
    code_blockt &init_code);

  refined_string_exprt convert_exprt_to_string_exprt(
    const exprt &deref,
    const source_locationt &loc,
    symbol_table_baset &symbol_table,
    code_blockt &init_code);

  exprt::operandst process_operands(
    const exprt::operandst &operands,
    const source_locationt &loc,
    symbol_table_baset &symbol_table,
    code_blockt &init_code);

  exprt::operandst process_equals_function_operands(
    const exprt::operandst &operands,
    const source_locationt &loc,
    symbol_table_baset &symbol_table,
    code_blockt &init_code);

  refined_string_exprt replace_char_array(
    const exprt &array_pointer,
    const source_locationt &loc,
    symbol_table_baset &symbol_table,
    code_blockt &code);

  symbol_exprt fresh_string(
    const typet &type,
    const source_locationt &loc,
    symbol_table_baset &symbol_table);

  symbol_exprt fresh_array(
    const typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  refined_string_exprt decl_string_expr(
    const source_locationt &loc,
    symbol_table_baset &symbol_table,
    code_blockt &code);

  refined_string_exprt make_nondet_string_expr(
    const source_locationt &loc,
    const irep_idt &function_id,
    symbol_table_baset &symbol_table,
    code_blockt &code);

  exprt allocate_fresh_string(
    const typet &type,
    const source_locationt &loc,
    const irep_idt &function_id,
    symbol_table_baset &symbol_table,
    code_blockt &code);

  exprt allocate_fresh_array(
    const typet &type,
    const source_locationt &loc,
    const irep_idt &function_id,
    symbol_tablet &symbol_table,
    code_blockt &code);

  codet code_return_function_application(
    const irep_idt &function_name,
    const exprt::operandst &arguments,
    const typet &type,
    symbol_table_baset &symbol_table);

  refined_string_exprt string_expr_of_function(
    const irep_idt &function_name,
    const exprt::operandst &arguments,
    const source_locationt &loc,
    symbol_table_baset &symbol_table,
    code_blockt &code);

  codet code_assign_components_to_java_string(
    const exprt &lhs,
    const exprt &rhs_array,
    const exprt &rhs_length,
    const symbol_table_baset &symbol_table);

  codet code_assign_string_expr_to_java_string(
    const exprt &lhs,
    const refined_string_exprt &rhs,
    const symbol_table_baset &symbol_table);

  void code_assign_java_string_to_string_expr(
    const refined_string_exprt &lhs,
    const exprt &rhs,
    const source_locationt &loc,
    const symbol_table_baset &symbol_table,
    code_blockt &code);

  refined_string_exprt string_literal_to_string_expr(
    const std::string &s,
    const source_locationt &loc,
    symbol_table_baset &symbol_table,
    code_blockt &code);

  codet make_function_from_call(
    const irep_idt &function_name,
    const java_method_typet &type,
    const source_locationt &loc,
    symbol_table_baset &symbol_table);

  codet make_init_function_from_call(
    const irep_idt &function_name,
    const java_method_typet &type,
    const source_locationt &loc,
    symbol_table_baset &symbol_table,
    bool ignore_first_arg = true);

  codet make_assign_and_return_function_from_call(
    const irep_idt &function_name,
    const java_method_typet &type,
    const source_locationt &loc,
    symbol_table_baset &symbol_table);

  codet make_assign_function_from_call(
    const irep_idt &function_name,
    const java_method_typet &type,
    const source_locationt &loc,
    symbol_table_baset &symbol_table);

  codet make_string_returning_function_from_call(
    const irep_idt &function_name,
    const java_method_typet &type,
    const source_locationt &loc,
    symbol_table_baset &symbol_table);

  exprt make_argument_for_format(
    const exprt &argv,
    std::size_t index,
    const struct_typet &structured_type,
    const source_locationt &loc,
    const irep_idt &function_id,
    symbol_table_baset &symbol_table,
    code_blockt &code);

  exprt get_primitive_value_of_object(
    const exprt &object,
    irep_idt type_name,
    const source_locationt &loc,
    symbol_table_baset &symbol_table,
    code_blockt &code);

  exprt get_object_at_index(const exprt &argv, std::size_t index);

  codet make_init_from_array_code(
    const java_method_typet &type,
    const source_locationt &loc,
    const irep_idt &function_id,
    symbol_table_baset &symbol_table);
};

exprt make_nondet_infinite_char_array(
  symbol_table_baset &symbol_table,
  const source_locationt &loc,
  const irep_idt &function_id,
  code_blockt &code);

void add_pointer_to_array_association(
  const exprt &pointer,
  const exprt &array,
  symbol_table_baset &symbol_table,
  const source_locationt &loc,
  code_blockt &code);

void add_array_to_length_association(
  const exprt &array,
  const exprt &length,
  symbol_table_baset &symbol_table,
  const source_locationt &loc,
  code_blockt &code);

void add_character_set_constraint(
  const exprt &pointer,
  const exprt &length,
  const irep_idt &char_set,
  symbol_table_baset &symbol_table,
  const source_locationt &loc,
  code_blockt &code);

#endif // CPROVER_JAVA_BYTECODE_JAVA_STRING_LIBRARY_PREPROCESS_H
