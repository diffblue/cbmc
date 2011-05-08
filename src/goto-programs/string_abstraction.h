/*******************************************************************\

Module: String Abstraction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_STRING_ABSTRACTION_H
#define CPROVER_GOTO_PROGRAMS_STRING_ABSTRACTION_H

#include <context.h>
#include <message_stream.h>
#include <config.h>
#include <bitvector.h>

#include "goto_functions.h"

/*******************************************************************\

   Class: string_abstractiont

 Purpose:

\*******************************************************************/

class string_abstractiont:public message_streamt
{
public:
  string_abstractiont(
    contextt &_context,
    message_handlert &_message_handler);
  
  void operator()(goto_programt &dest);
  void operator()(goto_functionst &dest);

  exprt is_zero_string(
    const exprt &object,
    bool write,
    const locationt &location);

  exprt zero_string_length(
    const exprt &object,
    bool write,
    const locationt &location);

  exprt buffer_size(
    const exprt &object,
    const locationt &location);

  static bool has_string_macros(const exprt &expr);

  void replace_string_macros(
    exprt &expr,
    bool lhs,
    const locationt &location);
  
  typet get_string_struct(void) { return string_struct; }

protected:
  contextt &context;
  namespacet ns;

  void move_lhs_arithmetic(exprt &lhs, exprt &rhs);

  bool is_char_type(const typet &type) const
  {
    if(type.id()==ID_symbol)
      return is_char_type(ns.follow(type));

    if(type.id()!=ID_signedbv &&
       type.id()!=ID_unsignedbv)
      return false;

    return bv_width(type)==config.ansi_c.char_width;
  }

  void make_type(exprt &dest, const typet &type)
  {
    if(dest.is_not_nil() &&
       ns.follow(dest.type())!=ns.follow(type))
      dest.make_typecast(type);
  }

  void abstract(goto_programt &dest, goto_programt::targett it);
  void abstract_assign(goto_programt &dest, goto_programt::targett it);
  void abstract_pointer_assign(goto_programt &dest, goto_programt::targett it);
  void abstract_char_assign(goto_programt &dest, goto_programt::targett it);
  void abstract_function_call(goto_programt &dest, goto_programt::targett it);

  typedef enum { IS_ZERO, LENGTH, SIZE } whatt;

  exprt build(
    const exprt &pointer,
    whatt what,
    bool write,
    const locationt &location);

  exprt build(const exprt &ptr, bool write);
  exprt build_symbol_ptr(const exprt &object);
  exprt build_symbol_buffer(const exprt &object);
  exprt build_symbol_constant(const irep_idt &str);
  exprt build_unknown(whatt what, bool write);
  exprt build_unknown(bool write);
  static typet build_type(whatt what);

  exprt sub(const exprt &a, const exprt &b)
  {
    if(b.is_nil() || b.is_zero()) return a;
    exprt result("-", a.type());
    result.copy_to_operands(a, b);
    make_type(result.op1(), result.type());
    return result;
  }

  exprt member(const exprt &a, whatt what);

  typet string_struct;
  goto_programt initialization;  

  typedef std::map<irep_idt, irep_idt> localst;
  localst locals;
  
  void abstract(goto_programt &dest);
};


// keep track of length of strings

void string_abstraction(
  contextt &context,
  message_handlert &message_handler,
  goto_programt &dest);

void string_abstraction(
  contextt &context,
  message_handlert &message_handler,
  goto_functionst &dest);

#endif
