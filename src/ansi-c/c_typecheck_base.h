/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_C_TYPECHECK_BASE_H
#define CPROVER_C_TYPECHECK_BASE_H

#include <util/symbol_table.h>
#include <util/typecheck.h>
#include <util/namespace.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include "ansi_c_declaration.h"
#include "designator.h"

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
    mode("C")
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
    mode("C")
  {
  }

  virtual ~c_typecheck_baset() { }

  virtual void typecheck()=0;
  virtual void typecheck_expr(exprt &expr);

protected:
  symbol_tablet &symbol_table;
  const irep_idt module;
  const irep_idt mode;
  irep_idt current_symbol_id;

  typedef hash_map_cont<irep_idt, typet, irep_id_hash> id_type_mapt;
  id_type_mapt parameter_map;
  
  // overload to use language specific syntax
  virtual std::string to_string(const exprt &expr);
  virtual std::string to_string(const typet &type);
  
  //
  // service functions
  //

  // initializers
  struct init_statet
  {
  protected:
    const exprt array;
    size_t pos;

  public:    
    explicit init_statet(const exprt &_array):array(_array), pos(0)
    {
    }
  
    size_t remaining() const
    {
      return array.operands().size()-pos;
    }
    
    bool has_next() const
    {
      return pos<array.operands().size();
    }
    
    init_statet &operator ++(int x)
    {
      pos++;
      return *this;
    }
    
    const exprt &operator *() const
    {
      return array.operands()[pos];
    }

    const exprt *operator ->() const
    {
      return &(array.operands()[pos]);
    }
  };
  
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

  virtual void do_designated_initializer(
    exprt &result,
    designatort &designator,
    const exprt &value,
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
  virtual void typecheck_asm(codet &code);
  virtual void typecheck_block(codet &code);
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
  virtual void typecheck_gcc_switch_case_range(codet &code);
  virtual void typecheck_gcc_local_label(codet &code);
  virtual void typecheck_return(codet &code);
  virtual void typecheck_switch(code_switcht &code);
  virtual void typecheck_while(code_whilet &code);
  virtual void typecheck_dowhile(code_dowhilet &code);
  virtual void typecheck_start_thread(codet &code);
  
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
  virtual void typecheck_expr_rel_vector(binary_relation_exprt &expr);
  virtual void adjust_float_rel(exprt &expr);
  virtual void typecheck_expr_index(exprt &expr);
  virtual void typecheck_expr_typecast(exprt &expr);
  virtual void typecheck_expr_symbol(exprt &expr);
  virtual void typecheck_expr_sizeof(exprt &expr);
  virtual void typecheck_expr_alignof(exprt &expr);
  virtual void typecheck_expr_function_identifier(exprt &expr);
  virtual void typecheck_side_effect_gcc_conditional_expression(side_effect_exprt &expr);
  virtual void typecheck_side_effect_function_call(side_effect_expr_function_callt &expr);
  virtual void typecheck_side_effect_assignment(side_effect_exprt &expr);
  virtual void typecheck_side_effect_statement_expression(side_effect_exprt &expr);
  virtual void typecheck_function_call_arguments(side_effect_expr_function_callt &expr);
  virtual exprt do_special_functions(side_effect_expr_function_callt &expr);

  virtual void make_index_type(exprt &expr);
  virtual void make_constant(exprt &expr);
  virtual void make_constant_index(exprt &expr);
  virtual void make_constant_rec(exprt &expr);
  
  virtual bool gcc_types_compatible_p(const typet &, const typet &);
  
  // types
  virtual void typecheck_type(typet &type);
  virtual void typecheck_compound_type(struct_union_typet &type);
  virtual void typecheck_compound_body(struct_union_typet &type);
  virtual void typecheck_c_enum_type(typet &type);
  virtual void typecheck_c_enum_tag_type(c_enum_tag_typet &type);
  virtual void typecheck_code_type(code_typet &type);
  virtual void typecheck_symbol_type(typet &type);
  virtual void typecheck_c_bit_field_type(c_bit_field_typet &type);
  virtual void typecheck_typeof_type(typet &type);
  virtual void typecheck_array_type(array_typet &type);
  virtual void typecheck_vector_type(vector_typet &type);
  virtual void typecheck_custom_type(typet &type);
  virtual void adjust_function_parameter(typet &type) const;
  virtual bool is_complete_type(const typet &type) const;
  
  void make_already_typechecked(typet &dest)
  {
    typet result(ID_already_typechecked);
    result.subtype().swap(dest);
    result.swap(dest);
  }

  // this cleans expressions in array types
  std::list<codet> clean_code;

  // environment
  void add_argc_argv(const symbolt &main_symbol);

  // symbol table management
  void move_symbol(symbolt &symbol, symbolt *&new_symbol);
  void move_symbol(symbolt &symbol)
  { symbolt *new_symbol; move_symbol(symbol, new_symbol); }
  
  // top-level stuff
  void typecheck_declaration(ansi_c_declarationt &);
  void typecheck_symbol(symbolt &symbol);
  void typecheck_new_symbol(symbolt &symbol);
  void typecheck_redefinition_type(symbolt &old_symbol, symbolt &new_symbol);
  void typecheck_redefinition_non_type(symbolt &old_symbol, symbolt &new_symbol);
  void typecheck_function_body(symbolt &symbol);

  virtual void do_initializer(symbolt &symbol);
  
  inline static bool is_numeric_type(const typet &src)
  {
    return src.id()==ID_complex ||
           src.id()==ID_unsignedbv ||
           src.id()==ID_signedbv ||
           src.id()==ID_floatbv || 
           src.id()==ID_fixedbv || 
           src.id()==ID_c_bool ||
           src.id()==ID_bool ||
           src.id()==ID_c_enum_tag ||
           src.id()==ID_c_bit_field;
  }
};

#endif
