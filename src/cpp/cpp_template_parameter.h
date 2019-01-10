/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/


#ifndef CPROVER_CPP_CPP_TEMPLATE_PARAMETER_H
#define CPROVER_CPP_CPP_TEMPLATE_PARAMETER_H

#include <util/expr.h>

// A data structure for expressions of the form
// <typename T, int x, ...>
// Not to be confused with template arguments!

struct template_parametert:public exprt
{
public:
  template_parametert():exprt(ID_template_parameter)
  {
  }

  #if 0
  bool get_is_type() const
  {
    return get_bool(ID_is_type);
  }

  void set_is_type(bool value)
  {
    set(ID_is_type, value);
  }

  irep_idt get_identifier() const
  {
    return get(ID_identifier);
  }

  void set_identifier(const irep_idt &identifier)
  {
    return set(ID_identifier, identifier);
  }
  #endif

  exprt &default_argument()
  {
    return static_cast<exprt &>(add(ID_C_default_value));
  }

  const exprt &default_argument() const
  {
    return static_cast<const exprt &>(find(ID_C_default_value));
  }

  bool has_default_argument() const
  {
    return find(ID_C_default_value).is_not_nil();
  }
};

/// a template parameter symbol that is a type
struct template_parameter_symbol_typet : public typet
{
public:
  explicit template_parameter_symbol_typet(const irep_idt &identifier)
    : typet(ID_template_parameter_symbol_type)
  {
    set_identifier(identifier);
  }

  void set_identifier(const irep_idt &identifier)
  {
    set(ID_identifier, identifier);
  }

  const irep_idt &get_identifier() const
  {
    return get(ID_identifier);
  }
};

/// \brief Cast a typet to a \ref template_parameter_symbol_typet.
///
/// This is an unchecked conversion. \a type must be known to be
/// \ref template_parameter_symbol_typet. Will fail with a
/// precondition violation if type doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref template_parameter_symbol_typet.
inline const template_parameter_symbol_typet &
to_template_parameter_symbol_type(const typet &type)
{
  PRECONDITION(type.id() == ID_template_parameter_symbol_type);
  return static_cast<const template_parameter_symbol_typet &>(type);
}

/// \copydoc to_template_parameter_symbol_type(const typet &)
inline template_parameter_symbol_typet &
to_template_parameter_symbol_type(typet &type)
{
  PRECONDITION(type.id() == ID_template_parameter_symbol_type);
  return static_cast<template_parameter_symbol_typet &>(type);
}

#endif // CPROVER_CPP_CPP_TEMPLATE_PARAMETER_H
