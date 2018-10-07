/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "format_type.h"
#include "format_expr.h"
#include "std_types.h"

#include <ostream>

/// format a \ref struct_typet
static std::ostream &format_rec(std::ostream &os, const struct_typet &src)
{
  os << "struct"
     << " {";
  bool first = true;

  for(const auto &c : src.components())
  {
    if(first)
      first = false;
    else
      os << ',';

    os << ' ' << format(c.type()) << ' ' << c.get_name();
  }

  return os << " }";
}

/// format a \ref union_typet
static std::ostream &format_rec(std::ostream &os, const union_typet &src)
{
  os << "union"
     << " {";
  bool first = true;

  for(const auto &c : src.components())
  {
    if(first)
      first = false;
    else
      os << ',';

    os << ' ' << format(c.type()) << ' ' << c.get_name();
  }

  return os << " }";
}

// The below generates a string in a generic syntax
// that is inspired by C/C++/Java, and is meant for debugging
// purposes.
std::ostream &format_rec(std::ostream &os, const typet &type)
{
  const auto &id = type.id();

  if(id == ID_pointer)
    return os << '*' << format(to_pointer_type(type).subtype());
  else if(id == ID_array)
  {
    const auto &t = to_array_type(type);
    if(t.is_complete())
      return os << format(t.subtype()) << '[' << format(t.size()) << ']';
    else
      return os << format(t.subtype()) << "[]";
  }
  else if(id == ID_struct)
    return format_rec(os, to_struct_type(type));
  else if(id == ID_union)
    return format_rec(os, to_union_type(type));
  else if(id == ID_union_tag)
    return os << "union " << to_union_tag_type(type).get_identifier();
  else if(id == ID_struct_tag)
    return os << "struct " << to_struct_tag_type(type).get_identifier();
  else if(id == ID_c_enum_tag)
    return os << "c_enum " << to_c_enum_tag_type(type).get_identifier();
  else if(id == ID_symbol_type)
    return os << "symbol_type " << to_symbol_type(type).get_identifier();
  else if(id == ID_signedbv)
    return os << "signedbv[" << to_signedbv_type(type).get_width() << ']';
  else if(id == ID_unsignedbv)
    return os << "unsignedbv[" << to_unsignedbv_type(type).get_width() << ']';
  else if(id == ID_floatbv)
    return os << "floatbv[" << to_floatbv_type(type).get_width() << ']';
  else if(id == ID_c_bool)
    return os << "c_bool[" << to_c_bool_type(type).get_width() << ']';
  else
    return os << id;
}
