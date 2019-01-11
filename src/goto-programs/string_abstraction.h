/*******************************************************************\

Module: String Abstraction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// String Abstraction

#ifndef CPROVER_GOTO_PROGRAMS_STRING_ABSTRACTION_H
#define CPROVER_GOTO_PROGRAMS_STRING_ABSTRACTION_H

#include <util/symbol_table.h>
#include <util/message.h>
#include <util/config.h>
#include <util/std_expr.h>

#include "goto_model.h"

class string_abstractiont:public messaget
{
public:
  string_abstractiont(
    symbol_tablet &_symbol_table,
    message_handlert &_message_handler);

  void operator()(goto_programt &dest);
  void operator()(goto_functionst &dest);

protected:
  const std::string arg_suffix;
  std::string sym_suffix;
  symbol_tablet &symbol_table;
  namespacet ns;
  unsigned temporary_counter;

  typedef ::std::map< typet, typet > abstraction_types_mapt;
  abstraction_types_mapt abstraction_types_map;

  ::std::set< irep_idt > current_args;

  static bool has_string_macros(const exprt &expr);

  void replace_string_macros(
    exprt &expr,
    bool lhs,
    const source_locationt &);

  void move_lhs_arithmetic(exprt &lhs, exprt &rhs);

  bool is_char_type(const typet &type) const
  {
    if(type.id()!=ID_signedbv &&
       type.id()!=ID_unsignedbv)
      return false;

    return to_bitvector_type(type).get_width()==config.ansi_c.char_width;
  }

  bool is_ptr_string_struct(const typet &type) const;

  void make_type(exprt &dest, const typet &type)
  {
    if(dest.is_not_nil() &&
       ns.follow(dest.type())!=ns.follow(type))
      dest.make_typecast(type);
  }

  goto_programt::targett abstract(
    goto_programt &dest, goto_programt::targett it);
  goto_programt::targett abstract_assign(
    goto_programt &dest, goto_programt::targett it);
  goto_programt::targett abstract_pointer_assign(
    goto_programt &dest, goto_programt::targett it);
  goto_programt::targett abstract_char_assign(
    goto_programt &dest, goto_programt::targett it);

  goto_programt::targett char_assign(
    goto_programt &dest,
    goto_programt::targett target,
    const exprt &new_lhs,
    const exprt &lhs,
    const exprt &rhs);

  void abstract_function_call(goto_programt::targett it);

  goto_programt::targett value_assignments(goto_programt &dest,
      goto_programt::targett it,
      const exprt &lhs, const exprt &rhs);

  goto_programt::targett value_assignments_if(
    goto_programt &dest,
    goto_programt::targett target,
    const exprt &lhs, const if_exprt &rhs);

  goto_programt::targett value_assignments_string_struct(
    goto_programt &dest,
    goto_programt::targett target,
    const exprt &lhs, const exprt &rhs);

  enum class whatt { IS_ZERO, LENGTH, SIZE };

  static typet build_type(whatt what);
  exprt build(
    const exprt &pointer,
    whatt what,
    bool write,
    const source_locationt &);

  bool build(const exprt &object, exprt &dest, bool write);
  bool build_wrap(const exprt &object, exprt &dest, bool write);
  bool build_if(const if_exprt &o_if, exprt &dest, bool write);
  bool build_array(const array_exprt &object, exprt &dest, bool write);
  bool build_symbol(const symbol_exprt &sym, exprt &dest);
  bool build_symbol_constant(const mp_integer &zero_length,
      const mp_integer &buf_size, exprt &dest);

  exprt build_unknown(whatt what, bool write);
  exprt build_unknown(const typet &type, bool write);
  const typet &build_abstraction_type(const typet &type);
  const typet &build_abstraction_type_rec(const typet &type,
      const abstraction_types_mapt &known);
  bool build_pointer(const exprt &object, exprt &dest, bool write);
  void build_new_symbol(const symbolt &symbol,
      const irep_idt &identifier, const typet &type);

  exprt member(const exprt &a, whatt what);

  typet string_struct;
  goto_programt initialization;

  typedef std::unordered_map<irep_idt, irep_idt> localst;
  localst locals;

  void abstract(goto_programt &dest);

  void add_str_arguments(
      const irep_idt &name,
      goto_functionst::goto_functiont &fct);

  void add_argument(
    code_typet::parameterst &str_args,
    const symbolt &fct_symbol,
    const typet &type,
    const irep_idt &base_name,
    const irep_idt &identifier);

  void make_decl_and_def(goto_programt &dest, goto_programt::targett ref_instr,
    const irep_idt &identifier, const irep_idt &source_sym);

  exprt make_val_or_dummy_rec(goto_programt &dest,
      goto_programt::targett ref_instr,
      const symbolt &symbol, const typet &source_type);

  symbol_exprt add_dummy_symbol_and_value(
    goto_programt &dest,
    goto_programt::targett ref_instr,
    const symbolt &symbol,
    const irep_idt &component_name,
    const typet &type,
    const typet &source_type);

  void declare_define_locals(goto_programt &dest);
};

// keep track of length of strings

void string_abstraction(
  goto_modelt &,
  message_handlert &);

void string_abstraction(
  symbol_tablet &,
  message_handlert &,
  goto_functionst &);

#endif // CPROVER_GOTO_PROGRAMS_STRING_ABSTRACTION_H
