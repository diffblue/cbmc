/*******************************************************************\

Module: Preprocess a goto-programs so that calls to the java String
        library are recognized by the PASS algorithm

Author: Romain Brenguier

Date:   September 2016

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_STRING_REFINE_PREPROCESS_H
#define CPROVER_GOTO_PROGRAMS_STRING_REFINE_PREPROCESS_H

#include <goto-programs/goto_model.h>
#include <util/ui_message.h>
#include <util/string_expr.h>

class string_refine_preprocesst:public messaget
{
 public:
  string_refine_preprocesst(
    symbol_tablet &, goto_functionst &, message_handlert &);

 private:
  namespacet ns;
  symbol_tablet & symbol_table;
  goto_functionst & goto_functions;

  typedef std::unordered_map<irep_idt, irep_idt, irep_id_hash> id_mapt;
  typedef std::unordered_map<exprt, exprt, irep_hash> expr_mapt;

  // Map name of Java string functions to there equivalent in the solver
  id_mapt side_effect_functions;
  id_mapt string_functions;
  id_mapt c_string_functions;
  id_mapt string_function_calls;

  std::unordered_map<irep_idt, std::string, irep_id_hash> signatures;

  // unique id for each newly created symbols
  int next_symbol_id;

  void initialize_string_function_table();

  static bool check_java_type(const typet &type, const std::string &tag);

  static bool is_java_string_pointer_type(const typet &type);

  static bool is_java_string_type(const typet &type);

  static bool is_java_string_builder_type(const typet &type);

  static bool is_java_string_builder_pointer_type(const typet &type);

  static bool is_java_char_sequence_type(const typet &type);

  static bool is_java_char_sequence_pointer_type(const typet &type);

  static bool is_java_char_array_type(const typet &type);

  static bool is_java_char_array_pointer_type(const typet &type);

  static bool implements_java_char_sequence(const typet &type)
  {
      return
        is_java_char_sequence_pointer_type(type) ||
        is_java_string_builder_pointer_type(type) ||
        is_java_string_pointer_type(type);
  }

  symbol_exprt fresh_array(
    const typet &type, const source_locationt &location);
  symbol_exprt fresh_string(
    const typet &type, const source_locationt &location);

  // get the data member of a java string
  static exprt get_data(const exprt &string, const typet &data_type)
  {
    return member_exprt(string, "data", data_type);
  }

  // get the length member of a java string
  exprt get_length(const exprt &string, const typet &length_type)
  {
    return member_exprt(string, "length", length_type);
  }

  // type of pointers to string
  pointer_typet jls_ptr;
  exprt replace_string(const exprt &in);
  exprt replace_string_in_assign(const exprt &in);

  void insert_assignments(
    goto_programt &goto_program,
    goto_programt::targett &target,
    irep_idt function,
    source_locationt location,
    const std::list<code_assignt> &va);

  exprt replace_string_pointer(const exprt &in);

  // Replace string builders by expression of the mapping and make
  // assignments for strings as string_exprt
  exprt::operandst process_arguments(
    goto_programt &goto_program,
    goto_programt::targett &target,
    const exprt::operandst &arguments,
    const source_locationt &location,
    const std::string &signature="");

  // Signature of the named function if it is defined in the signature map,
  // empty string otherwise
  std::string function_signature(const irep_idt &function_id);

  void declare_function(irep_idt function_name, const typet &type);

  void get_data_and_length_type_of_string(
    const exprt &expr, typet &data_type, typet &length_type);

  void get_data_and_length_type_of_char_array(
    const exprt &expr, typet &data_type, typet &length_type);

  function_application_exprt build_function_application(
    const irep_idt &function_name,
    const typet &type,
    const source_locationt &location,
    const exprt::operandst &arguments);

  void make_normal_assign(
    goto_programt &goto_program,
    goto_programt::targett target,
    const exprt &lhs,
    const code_typet &function_type,
    const irep_idt &function_name,
    const exprt::operandst &arguments,
    const source_locationt &location,
    const std::string &signature="");

  void make_string_assign(
    goto_programt &goto_program,
    goto_programt::targett &target,
    const exprt &lhs,
    const code_typet &function_type,
    const irep_idt &function_name,
    const exprt::operandst &arguments,
    const source_locationt &location,
    const std::string &signature);

  exprt make_cprover_string_assign(
    goto_programt &goto_program,
    goto_programt::targett &target,
    const exprt &rhs,
    const source_locationt &location);

  string_exprt make_cprover_char_array_assign(
    goto_programt &goto_program,
    goto_programt::targett &target,
    const exprt &rhs,
    const source_locationt &location);

  void make_string_function(
    goto_programt &goto_program,
    goto_programt::targett &target,
    const irep_idt &function_name,
    const std::string &signature,
    bool assign_first_arg=false,
    bool skip_first_arg=false);

  void make_string_function(
    goto_programt &goto_program,
    goto_programt::targett &target,
    const exprt &lhs,
    const code_typet &function_type,
    const irep_idt &function_name,
    const exprt::operandst &arguments,
    const source_locationt &location,
    const std::string &signature);

  void make_string_function_call(
    goto_programt &goto_program,
    goto_programt::targett &target,
    const irep_idt &function_name,
    const std::string &signature);

  void make_string_function_side_effect(
    goto_programt &goto_program,
    goto_programt::targett &target,
    const irep_idt &function_name,
    const std::string &signature);

  void make_to_char_array_function(
    goto_programt &goto_program, goto_programt::targett &);

  void replace_string_calls(goto_functionst::function_mapt::iterator f_it);
};

#endif
