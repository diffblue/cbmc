/*******************************************************************\

Module: ANSI-CC Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_DECLARATION_H
#define CPROVER_ANSI_C_DECLARATION_H

#include <cassert>

#include <util/symbol.h>

class ansi_c_declarationt:public exprt
{
public:
  ansi_c_declarationt();
  
  exprt &value()
  {
    return static_cast<exprt &>(add(ID_value));
  }
  
  const exprt &value() const
  {
    return static_cast<const exprt &>(find(ID_value));
  }
  
  void set_name(const irep_idt &name)
  {
    return set(ID_name, name);
  }
  
  irep_idt get_name() const
  {
    return get(ID_name);
  }
  
  irep_idt get_base_name() const
  {
    return get(ID_base_name);
  }
  
  void set_base_name(const irep_idt &base_name)
  {
    return set(ID_base_name, base_name);
  }
  
  bool get_is_type() const
  {
    return get_bool(ID_is_type);
  }
  
  void set_is_type(bool is_type)
  {
    set(ID_is_type, is_type);
  }
  
  bool get_is_typedef() const
  {
    return get_bool(ID_is_typedef);
  }
  
  void set_is_typedef(bool is_typedef)
  {
    set(ID_is_typedef, is_typedef);
  }
  
  bool get_is_macro() const
  {
    return get_bool(ID_is_macro);
  }
  
  void set_is_macro(bool is_macro)
  {
    set(ID_is_macro, is_macro);
  }
  
  bool get_is_static() const
  {
    return get_bool(ID_is_static);
  }
  
  void set_is_static(bool is_static)
  {
    set(ID_is_static, is_static);
  }
  
  bool get_is_parameter() const
  {
    return get_bool(ID_is_parameter);
  }
  
  void set_is_parameter(bool is_parameter)
  {
    set(ID_is_parameter, is_parameter);
  }
  
  bool get_is_global() const
  {
    return get_bool(ID_is_global);
  }
  
  void set_is_global(bool is_global)
  {
    set(ID_is_global, is_global);
  }
  
  bool get_is_register() const
  {
    return get_bool(ID_is_register);
  }
  
  void set_is_register(bool is_register)
  {
    set(ID_is_register, is_register);
  }
  
  bool get_is_thread_local() const
  {
    return get_bool(ID_is_thread_local);
  }
  
  void set_is_thread_local(bool is_thread_local)
  {
    set(ID_is_thread_local, is_thread_local);
  }
  
  bool get_is_inline() const
  {
    return get_bool(ID_is_inline);
  }
  
  void set_is_inline(bool is_inline)
  {
    set(ID_is_inline, is_inline);
  }
  
  bool get_is_extern() const
  {
    return get_bool(ID_is_extern);
  }
  
  void set_is_extern(bool is_extern)
  {
    set(ID_is_extern, is_extern);
  }
  
  bool get_is_static_assert() const
  {
    return get_bool(ID_is_static_assert);
  }
  
  void set_is_static_assert(bool is_static_assert)
  {
    set(ID_is_static_assert, is_static_assert);
  }
  
  void to_symbol(symbolt &symbol) const;
};

extern inline ansi_c_declarationt &to_ansi_c_declaration(exprt &expr)
{
  assert(expr.id()==ID_declaration);
  return static_cast<ansi_c_declarationt &>(expr);
}

extern inline const ansi_c_declarationt &to_ansi_c_declaration(const exprt &expr)
{
  assert(expr.id()==ID_declaration);
  return static_cast<const ansi_c_declarationt &>(expr);
}

#endif
