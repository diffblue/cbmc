/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Language Type Checking

#ifndef CPROVER_ANSI_C_C_TYPECHECK_BASE_H
#define CPROVER_ANSI_C_C_TYPECHECK_BASE_H

#include <util/namespace.h>
#include <util/std_code.h>
#include <util/symbol_table.h>
#include <util/typecheck.h>

#include "designator.h"

class ansi_c_declarationt;
class c_bit_field_typet;
class shift_exprt;

class c_typecheck_baset:
  public typecheckt,
  public namespacet
{
public:
  c_typecheck_baset(
    symbol_tablet &_symbol_table,
    const std::string &_module,
    message_handlert &_message_handler):
    typecheckt(_message_handler),
    namespacet(_symbol_table),
    symbol_table(_symbol_table),
    module(_module),
    mode(ID_C),
    break_is_allowed(false),
    continue_is_allowed(false),
    case_is_allowed(false)
  {
  }

  c_typecheck_baset(
    symbol_tablet &_symbol_table1,
    const symbol_tablet &_symbol_table2,
    const std::string &_module,
    message_handlert &_message_handler):
    typecheckt(_message_handler),
    namespacet(_symbol_table1, _symbol_table2),
    symbol_table(_symbol_table1),
    module(_module),
    mode(ID_C),
    break_is_allowed(false),
    continue_is_allowed(false),
    case_is_allowed(false)
  {
  }

  virtual ~c_typecheck_baset() { }

  virtual void typecheck()=0;
  virtual void typecheck_expr(exprt &expr);

protected:
  symbol_tablet &symbol_table;
  const irep_idt module;
  const irep_idt mode;
  symbolt current_symbol;

  typedef std::unordered_map<irep_idt, typet> id_type_mapt;
  id_type_mapt parameter_map;

  // overload to use language specific syntax
  virtual std::string to_string(const exprt &expr);
  virtual std::string to_string(const typet &type);

  //
  // service functions
  //

  virtual void do_initializer(
    exprt &initializer,
    const typet &type,
    bool force_constant);

  virtual exprt do_initializer_rec(
    const exprt &value,
    const typet &type,
    bool force_constant);

  virtual exprt do_initializer_list(
    const exprt &value,
    const typet &type,
    bool force_constant);

  virtual exprt::operandst::const_iterator do_designated_initializer(
    exprt &result,
    designatort &designator,
    const exprt &initializer_list,
    exprt::operandst::const_iterator init_it,
    bool force_constant);

  designatort make_designator(const typet &type, const exprt &src);
  void designator_enter(const typet &type, designatort &designator); // go down
  void increment_designator(designatort &designator);

  // typecasts

  bool gcc_vector_types_compatible(const vector_typet &, const vector_typet &);

  virtual void implicit_typecast(exprt &expr, const typet &type);
  virtual void implicit_typecast_arithmetic(exprt &expr);
  virtual void implicit_typecast_arithmetic(exprt &expr1, exprt &expr2);

  virtual void implicit_typecast_bool(exprt &expr)
  {
    implicit_typecast(expr, bool_typet());
  }

  // code
  virtual void start_typecheck_code();
  virtual void typecheck_code(codet &code);

  virtual void typecheck_assign(codet &expr);
  virtual void typecheck_asm(code_asmt &code);
  virtual void typecheck_block(code_blockt &code);
  virtual void typecheck_break(codet &code);
  virtual void typecheck_continue(codet &code);
  virtual void typecheck_decl(codet &code);
  virtual void typecheck_expression(codet &code);
  virtual void typecheck_for(codet &code);
  virtual void typecheck_goto(code_gotot &code);
  virtual void typecheck_ifthenelse(code_ifthenelset &code);
  virtual void typecheck_label(code_labelt &code);
  virtual void typecheck_switch_case(code_switch_caset &code);
  virtual void typecheck_gcc_computed_goto(codet &code);
  virtual void typecheck_gcc_switch_case_range(code_gcc_switch_case_ranget &);
  virtual void typecheck_gcc_local_label(codet &code);
  virtual void typecheck_return(code_frontend_returnt &);
  virtual void typecheck_switch(codet &code);
  virtual void typecheck_while(code_whilet &code);
  virtual void typecheck_dowhile(code_dowhilet &code);
  virtual void typecheck_start_thread(codet &code);

  // contracts
  virtual void typecheck_spec_assigns(exprt::operandst &targets);
  virtual void typecheck_spec_assigns_condition(exprt &condition);
  virtual void typecheck_spec_assigns_target(exprt &target);
  virtual void typecheck_spec_loop_invariant(codet &code);
  virtual void typecheck_spec_decreases(codet &code);

  bool break_is_allowed;
  bool continue_is_allowed;
  bool case_is_allowed;
  typet switch_op_type;
  typet return_type;

  // to check that all labels used are also defined
  std::map<irep_idt, source_locationt> labels_defined, labels_used;

  // expressions
  virtual void typecheck_expr_builtin_va_arg(exprt &expr);
  virtual void typecheck_expr_builtin_offsetof(exprt &expr);
  virtual void typecheck_expr_cw_va_arg_typeof(exprt &expr);
  virtual void typecheck_expr_main(exprt &expr);
  virtual void typecheck_expr_operands(exprt &expr);
  virtual void typecheck_expr_comma(exprt &expr);
  virtual void typecheck_expr_constant(exprt &expr);
  virtual void typecheck_expr_side_effect(side_effect_exprt &expr);
  virtual void typecheck_expr_unary_arithmetic(exprt &expr);
  virtual void typecheck_expr_unary_boolean(exprt &expr);
  virtual void typecheck_expr_binary_arithmetic(exprt &expr);
  virtual void typecheck_expr_shifts(shift_exprt &expr);
  virtual void typecheck_expr_pointer_arithmetic(exprt &expr);
  virtual void typecheck_arithmetic_pointer(const exprt &expr);
  virtual void typecheck_expr_binary_boolean(exprt &expr);
  virtual void typecheck_expr_trinary(if_exprt &expr);
  virtual void typecheck_expr_address_of(exprt &expr);
  virtual void typecheck_expr_dereference(exprt &expr);
  virtual void typecheck_expr_member(exprt &expr);
  virtual void typecheck_expr_ptrmember(exprt &expr);
  virtual void typecheck_expr_rel(binary_relation_exprt &expr);
  virtual void typecheck_expr_rel_vector(binary_exprt &expr);
  virtual void adjust_float_rel(binary_relation_exprt &);
  static void add_rounding_mode(exprt &);
  virtual void typecheck_expr_index(exprt &expr);
  virtual void typecheck_expr_typecast(exprt &expr);
  virtual void typecheck_expr_symbol(exprt &expr);
  virtual void typecheck_expr_sizeof(exprt &expr);
  virtual void typecheck_expr_alignof(exprt &expr);
  virtual void typecheck_expr_function_identifier(exprt &expr);
  virtual void typecheck_side_effect_gcc_conditional_expression(
    side_effect_exprt &expr);
  virtual void typecheck_side_effect_function_call(
    side_effect_expr_function_callt &expr);
  virtual void typecheck_side_effect_assignment(side_effect_exprt &expr);
  virtual void typecheck_side_effect_statement_expression(
    side_effect_exprt &expr);
  virtual void typecheck_function_call_arguments(
    side_effect_expr_function_callt &expr);
  virtual exprt do_special_functions(side_effect_expr_function_callt &expr);
  exprt typecheck_builtin_overflow(
    side_effect_expr_function_callt &expr,
    const irep_idt &arith_op);
  exprt
  typecheck_saturating_arithmetic(const side_effect_expr_function_callt &expr);
  virtual optionalt<symbol_exprt> typecheck_gcc_polymorphic_builtin(
    const irep_idt &identifier,
    const exprt::operandst &arguments,
    const source_locationt &source_location);
  virtual code_blockt instantiate_gcc_polymorphic_builtin(
    const irep_idt &identifier,
    const symbol_exprt &function_symbol);
  virtual exprt
  typecheck_shuffle_vector(const side_effect_expr_function_callt &expr);
  void disallow_subexpr_by_id(
    const exprt &,
    const irep_idt &,
    const std::string &) const;

  virtual void make_index_type(exprt &expr);
  virtual void make_constant(exprt &expr);
  virtual void make_constant_index(exprt &expr);

  virtual bool gcc_types_compatible_p(const typet &, const typet &);

  // types
  virtual void typecheck_type(typet &type);
  virtual void typecheck_compound_type(struct_union_typet &type);
  virtual void typecheck_compound_body(struct_union_typet &type);
  virtual void typecheck_c_enum_type(typet &type);
  virtual void typecheck_c_enum_tag_type(c_enum_tag_typet &type);
  virtual void typecheck_code_type(code_typet &type);
  virtual void typecheck_typedef_type(typet &type);
  virtual void typecheck_c_bit_field_type(c_bit_field_typet &type);
  virtual void typecheck_typeof_type(typet &type);
  virtual void typecheck_array_type(array_typet &type);
  virtual void typecheck_vector_type(typet &type);
  virtual void typecheck_custom_type(typet &type);
  virtual void adjust_function_parameter(typet &type) const;
  virtual bool is_complete_type(const typet &type) const;

  typet enum_constant_type(
    const mp_integer &min, const mp_integer &max) const;

  bitvector_typet enum_underlying_type(
    const mp_integer &min,
    const mp_integer &max,
    bool is_packed) const;

  // this cleans expressions in array types
  std::list<codet> clean_code;

  // symbol table management
  void move_symbol(symbolt &symbol, symbolt *&new_symbol);
  void move_symbol(symbolt &symbol)
  { symbolt *new_symbol; move_symbol(symbol, new_symbol); }

  // top-level stuff
  void typecheck_declaration(ansi_c_declarationt &);
  void typecheck_symbol(symbolt &symbol);
  void typecheck_new_symbol(symbolt &symbol);
  void typecheck_redefinition_type(symbolt &old_symbol, symbolt &new_symbol);
  void typecheck_redefinition_non_type(
    symbolt &old_symbol, symbolt &new_symbol);
  void typecheck_function_body(symbolt &symbol);

  /// Create symbols for parameter of the code-typed symbol \p symbol.
  void add_parameters_to_symbol_table(symbolt &symbol);

  virtual void do_initializer(symbolt &symbol);

  static bool is_numeric_type(const typet &src)
  {
    return src.id()==ID_complex ||
           src.id()==ID_unsignedbv ||
           src.id()==ID_signedbv ||
           src.id()==ID_floatbv ||
           src.id()==ID_fixedbv ||
           src.id()==ID_c_bool ||
           src.id()==ID_bool ||
           src.id()==ID_c_enum_tag ||
           src.id()==ID_c_bit_field ||
           src.id()==ID_integer ||
           src.id()==ID_real;
  }

  typedef std::unordered_map<irep_idt, irep_idt> asm_label_mapt;
  asm_label_mapt asm_label_map;

  void apply_asm_label(const irep_idt &asm_label, symbolt &symbol);
};

class already_typechecked_exprt : public expr_protectedt
{
public:
  explicit already_typechecked_exprt(exprt expr)
    : expr_protectedt(ID_already_typechecked, typet{}, {std::move(expr)})
  {
  }

  static void make_already_typechecked(exprt &expr)
  {
    already_typechecked_exprt a{expr};
    expr.swap(a);
  }

  exprt &get_expr()
  {
    return op0();
  }
};

class already_typechecked_typet : public type_with_subtypet
{
public:
  explicit already_typechecked_typet(typet type)
    : type_with_subtypet(ID_already_typechecked, std::move(type))
  {
  }

  static void make_already_typechecked(typet &type)
  {
    already_typechecked_typet a{type};
    type.swap(a);
  }

  typet &get_type()
  {
    return subtype();
  }
};

inline already_typechecked_exprt &to_already_typechecked_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_already_typechecked);
  PRECONDITION(expr.operands().size() == 1);

  return static_cast<already_typechecked_exprt &>(expr);
}

inline already_typechecked_typet &to_already_typechecked_type(typet &type)
{
  PRECONDITION(type.id() == ID_already_typechecked);
  PRECONDITION(type.has_subtype());

  return static_cast<already_typechecked_typet &>(type);
}

#endif // CPROVER_ANSI_C_C_TYPECHECK_BASE_H
