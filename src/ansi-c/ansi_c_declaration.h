/*******************************************************************\

Module: ANSI-CC Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-CC Language Type Checking

#ifndef CPROVER_ANSI_C_ANSI_C_DECLARATION_H
#define CPROVER_ANSI_C_ANSI_C_DECLARATION_H

#include <cassert>

#include <util/std_expr.h>
#include <util/symbol.h>

class ansi_c_declaratort : public nullary_exprt
{
public:
  ansi_c_declaratort() : nullary_exprt(ID_declarator)
  {
  }

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

  void build(irept &src);
};

inline ansi_c_declaratort &to_ansi_c_declarator(exprt &expr)
{
  assert(expr.id()==ID_declarator);
  return static_cast<ansi_c_declaratort &>(expr);
}

inline const ansi_c_declaratort &to_ansi_c_declarator(const exprt &expr)
{
  assert(expr.id()==ID_declarator);
  return static_cast<const ansi_c_declaratort &>(expr);
}

class ansi_c_declarationt:public exprt
{
public:
  ansi_c_declarationt():exprt(ID_declaration)
  {
  }

  bool get_is_typedef() const
  {
    return get_bool(ID_is_typedef);
  }

  void set_is_typedef(bool is_typedef)
  {
    set(ID_is_typedef, is_typedef);
  }

  bool get_is_enum_constant() const
  {
    return get_bool(ID_is_enum_constant);
  }

  void set_is_enum_constant(bool is_enum_constant)
  {
    set(ID_is_enum_constant, is_enum_constant);
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

  bool get_is_member() const
  {
    return get_bool(ID_is_member);
  }

  void set_is_member(bool is_member)
  {
    set(ID_is_member, is_member);
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

  bool get_is_weak() const
  {
    return get_bool(ID_is_weak);
  }

  void set_is_weak(bool is_weak)
  {
    set(ID_is_weak, is_weak);
  }

  bool get_is_used() const
  {
    return get_bool(ID_is_used);
  }

  void set_is_used(bool is_used)
  {
    set(ID_is_used, is_used);
  }

  void to_symbol(
    const ansi_c_declaratort &,
    symbolt &symbol) const;

  typet full_type(const ansi_c_declaratort &) const;

  typedef std::vector<ansi_c_declaratort> declaratorst;

  const declaratorst &declarators() const
  {
    return (const declaratorst &)operands();
  }

  declaratorst &declarators()
  {
    return (declaratorst &)operands();
  }

  // special case of a declaration with exactly one declarator
  const ansi_c_declaratort &declarator() const
  {
    assert(declarators().size()==1);
    return declarators()[0];
  }

  ansi_c_declaratort &declarator()
  {
    assert(declarators().size()==1);
    return declarators()[0];
  }

  void output(std::ostream &) const;

  void add_initializer(exprt &value)
  {
    assert(!declarators().empty());
    declarators().back().value().swap(value);
  }
};

inline ansi_c_declarationt &to_ansi_c_declaration(exprt &expr)
{
  assert(expr.id()==ID_declaration);
  return static_cast<ansi_c_declarationt &>(expr);
}

inline const ansi_c_declarationt &to_ansi_c_declaration(const exprt &expr)
{
  assert(expr.id()==ID_declaration);
  return static_cast<const ansi_c_declarationt &>(expr);
}

#endif // CPROVER_ANSI_C_ANSI_C_DECLARATION_H
