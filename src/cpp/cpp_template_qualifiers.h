/// Author: Michael Tautschnig
/// \file
/// Recursive cv-qualifier comparison for template specialization matching

#ifndef CPROVER_CPP_CPP_TEMPLATE_QUALIFIERS_H
#define CPROVER_CPP_CPP_TEMPLATE_QUALIFIERS_H

#include <util/std_types.h>

/// Check that cv-qualifiers (C_constant, C_volatile) match recursively
/// throughout the type tree. irept::operator== ignores #-prefixed
/// attributes, so types like `const int*` and `int*` compare equal.
/// This function catches such differences in nested subtypes -- including
/// the return and parameter types of a function type (N5008 [dcl.fct]/6-7:
/// `void (*)(const int *)` and `void (*)(int *)` are distinct types, and so
/// are `int (S::*)(int) const` and `int (S::*)(int)`, whose
/// cv-qualifier-seq is the cv of the implicit object parameter's pointee).
inline bool qualifiers_match_recursively(const typet &a, const typet &b)
{
  if(
    a.get_bool(ID_C_constant) != b.get_bool(ID_C_constant) ||
    a.get_bool(ID_C_volatile) != b.get_bool(ID_C_volatile))
  {
    return false;
  }

  if(a.id() == ID_code && b.id() == ID_code)
  {
    const code_typet &ca = to_code_type(a);
    const code_typet &cb = to_code_type(b);
    if(!qualifiers_match_recursively(ca.return_type(), cb.return_type()))
      return false;
    if(ca.parameters().size() == cb.parameters().size())
    {
      for(std::size_t i = 0; i < ca.parameters().size(); i++)
      {
        if(!qualifiers_match_recursively(
             ca.parameters()[i].type(), cb.parameters()[i].type()))
          return false;
      }
    }
    return true;
  }

  const auto &a_sub = a.get_sub();
  const auto &b_sub = b.get_sub();
  if(a_sub.size() == b_sub.size())
  {
    for(std::size_t i = 0; i < a_sub.size(); i++)
    {
      if(
        a_sub[i].id() == b_sub[i].id() &&
        !qualifiers_match_recursively(
          static_cast<const typet &>(a_sub[i]),
          static_cast<const typet &>(b_sub[i])))
      {
        return false;
      }
    }
  }

  return true;
}

#endif // CPROVER_CPP_CPP_TEMPLATE_QUALIFIERS_H
