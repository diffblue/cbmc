/// Author: Michael Tautschnig
/// \file
/// Recursive cv-qualifier comparison for template specialization matching

#ifndef CPROVER_CPP_CPP_TEMPLATE_QUALIFIERS_H
#define CPROVER_CPP_CPP_TEMPLATE_QUALIFIERS_H

#include <util/std_types.h>

/// N5008 [basic.fundamental]/1, /8-9: char, signed char and unsigned char,
/// wchar_t, char16_t and char32_t, and long and long long are distinct types
/// even where they have the same representation (wchar_t and int, char16_t
/// and unsigned short).  The front end represents them by the same bit-vector
/// type with a different `\#c_type' comment, which irept::operator== ignores.
/// \return false if \p a and \p b are integer or floating-point types naming
///   different fundamental types
inline bool same_fundamental_type_name(const typet &a, const typet &b)
{
  if(
    a.id() != b.id() ||
    (a.id() != ID_signedbv && a.id() != ID_unsignedbv && a.id() != ID_floatbv))
  {
    return true;
  }
  const irep_idt &a_name = a.get(ID_C_c_type);
  const irep_idt &b_name = b.get(ID_C_c_type);
  return a_name.empty() || b_name.empty() || a_name == b_name;
}

/// Check that cv-qualifiers (C_constant, C_volatile) match recursively
/// throughout the type tree. irept::operator== ignores #-prefixed
/// attributes, so types like `const int*` and `int*` compare equal.
/// It also distinguishes the fundamental types same_fundamental_type_name
/// tells apart.
/// This function catches such differences in nested subtypes -- including
/// the return and parameter types of a function type (N5008 [dcl.fct]/6-7:
/// `void (*)(const int *)` and `void (*)(int *)` are distinct types, and so
/// are `int (S::*)(int) const` and `int (S::*)(int)`, whose
/// cv-qualifier-seq is the cv of the implicit object parameter's pointee).
inline bool qualifiers_match_recursively(const typet &a, const typet &b)
{
  // N5008 [basic.type.qualifier]/3: an array type whose elements are
  // cv-qualified has the cv-qualification of its elements, and cv-qualifiers
  // applied to an array type attach to its element type.  The front end
  // records them on the array node, on the element type, or both (`const T'
  // with T = char[3] marks the array, `const char[3]' both), so compare the
  // element types with the array's qualifiers pushed down to them.
  if(a.id() == ID_array && b.id() == ID_array)
  {
    const auto pushed_down = [](const typet &array)
    {
      typet element = to_array_type(array).element_type();
      if(array.get_bool(ID_C_constant))
        element.set(ID_C_constant, true);
      if(array.get_bool(ID_C_volatile))
        element.set(ID_C_volatile, true);
      return element;
    };
    return qualifiers_match_recursively(pushed_down(a), pushed_down(b));
  }

  if(
    a.get_bool(ID_C_constant) != b.get_bool(ID_C_constant) ||
    a.get_bool(ID_C_volatile) != b.get_bool(ID_C_volatile))
  {
    return false;
  }

  if(!same_fundamental_type_name(a, b))
    return false;

  // N5008 [dcl.ref]/1, [dcl.ptr]/1: a pointer, an lvalue reference and an
  // rvalue reference to the same type are distinct types.  References are
  // pointers carrying #reference / #rvalue_reference here, attributes that
  // irept::operator== also ignores.
  if(
    a.id() == ID_pointer && b.id() == ID_pointer &&
    (a.get_bool(ID_C_reference) != b.get_bool(ID_C_reference) ||
     a.get_bool(ID_C_rvalue_reference) != b.get_bool(ID_C_rvalue_reference)))
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
