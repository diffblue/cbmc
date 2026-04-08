/// \file
/// Recursive cv-qualifier comparison for template specialization matching

#ifndef CPROVER_CPP_CPP_TEMPLATE_QUALIFIERS_H
#define CPROVER_CPP_CPP_TEMPLATE_QUALIFIERS_H

#include <util/type.h>

/// Check that cv-qualifiers (C_constant, C_volatile) match recursively
/// throughout the type tree. irept::operator== ignores #-prefixed
/// attributes, so types like `const int*` and `int*` compare equal.
/// This function catches such differences in nested subtypes.
inline bool qualifiers_match_recursively(const typet &a, const typet &b)
{
  if(
    a.get_bool(ID_C_constant) != b.get_bool(ID_C_constant) ||
    a.get_bool(ID_C_volatile) != b.get_bool(ID_C_volatile))
  {
    return false;
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
