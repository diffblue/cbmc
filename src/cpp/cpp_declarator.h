/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_CPP_DECLARATOR_H
#define CPROVER_CPP_CPP_DECLARATOR_H

#include <util/expr.h>

#include "cpp_name.h"

class cpp_declaratort:public exprt
{
public:
  cpp_declaratort():exprt(ID_cpp_declarator)
  {
    value().make_nil();
    name().make_nil();
    add_source_location().make_nil();
  }

  explicit cpp_declaratort(const typet &type):exprt(ID_cpp_declarator, type)
  {
    value().make_nil();
    name().make_nil();
    add_source_location().make_nil();
  }

  cpp_namet &name() { return static_cast<cpp_namet &>(add(ID_name)); }
  const cpp_namet &name() const
  {
    return static_cast<const cpp_namet &>(find(ID_name));
  }

  exprt &value() { return static_cast<exprt &>(add(ID_value)); }
  const exprt &value() const
  {
    return static_cast<const exprt &>(find(ID_value));
  }

  // initializers for function arguments
  exprt &init_args()
  {
    return static_cast<exprt &>(add(ID_init_args));
  }
  const exprt &init_args() const
  {
    return static_cast<const exprt &>(find(ID_init_args));
  }

  irept &method_qualifier() { return add(ID_method_qualifier); }
  const irept &method_qualifier() const { return find(ID_method_qualifier); }

  irept &member_initializers() { return add(ID_member_initializers); }
  const irept &member_initializers() const
  {
    return find(ID_member_initializers);
  }

  irept &throw_decl()
  {
    return add(ID_throw_decl);
  }
  const irept &throw_decl() const
  {
    return find(ID_throw_decl);
  }

  void output(std::ostream &out) const;

  typet merge_type(const typet &declaration_type) const;
};

#endif // CPROVER_CPP_CPP_DECLARATOR_H
