/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "format_expr.h"
#include "format_type.h"
#include "std_types.h"

#include <ostream>

/// format a \ref struct_typet
static std::ostream &format_rec(
  std::ostream &os,
  const struct_typet &src)
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

// The below generates a string in a generic syntax
// that is inspired by C/C++/Java, and is meant for debugging
// purposes.
std::ostream &format_rec(std::ostream &os, const typet &type)
{
  const auto &id = type.id();

  if(id == ID_pointer)
    return os << '*' << format(type.subtype());
  else if(id == ID_array)
  {
    const auto &t = to_array_type(type);
    if(t.is_complete())
      return os << format(type.subtype()) << '[' << format(t.size()) << ']';
    else
      return os << format(type.subtype()) << "[]";
  }
  else if(id == ID_struct)
    return format_rec(os, to_struct_type(type));
  else if(id == ID_symbol)
    return os << "symbol_type " << to_symbol_type(type).get_identifier();
  else
    return os << id;
}
