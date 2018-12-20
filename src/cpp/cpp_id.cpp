/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_id.h"

#include <ostream>

#include <util/invariant.h>

#include "cpp_scope.h"

cpp_idt::cpp_idt():
  is_member(false),
  is_method(false),
  is_static_member(false),
  is_scope(false),
  is_constructor(false),
  id_class(id_classt::UNKNOWN),
  this_expr(static_cast<const exprt &>(get_nil_irep())),
  compound_counter(0),
  parent(nullptr)
{
}

void cpp_idt::print(std::ostream &out, unsigned indent) const
{
  print_fields(out, indent);

  if(!sub.empty())
  {
    for(const auto &s : sub)
      s.second.print(out, indent + 2);

    out << '\n';
  }
}

void cpp_idt::print_fields(std::ostream &out, unsigned indent) const
{
  out << std::string(indent, ' ');
  out << "**identifier=" << identifier << '\n';

  out << std::string(indent, ' ');
  out << "  prefix=" << prefix << '\n';

  out << std::string(indent, ' ');
  out << "  suffix=" << suffix << '\n';

  out << std::string(indent, ' ');
  out << "  base_name=" << base_name << '\n';

  out << std::string(indent, ' ');
  out << "  method=" << is_method << '\n';

  out << std::string(indent, ' ');
  out << "  class_identifier=" << class_identifier << '\n';

  for(const auto &s : secondary_scopes)
  {
    out << std::string(indent, ' ');
    out << "  secondary_scope=" << s->identifier << '\n';
  }

  for(const auto &s : using_scopes)
  {
    out << std::string(indent, ' ');
    out << "  using_scope=" << s->identifier << '\n';
  }

  out << std::string(indent, ' ');
  out << "  flags:";
  if(is_constructor)
    out << " constructor";
  if(is_scope)
    out << " scope";
  if(is_member)
    out << " member";
  if(is_static_member)
    out << " static_member";
  out << '\n';

  out << std::string(indent, ' ');
  out << "  id_class=" << id_class << '\n';
}

std::ostream &operator<<(std::ostream &out, const cpp_idt &cpp_id)
{
  cpp_id.print(out, 0);
  return out;
}

std::ostream &operator<<(std::ostream &out, const cpp_idt::id_classt &id_class)
{
  switch(id_class)
  {
  case cpp_idt::id_classt::UNKNOWN:           return out<<"UNKNOWN";
  case cpp_idt::id_classt::SYMBOL:            return out<<"SYMBOL";
  case cpp_idt::id_classt::TYPEDEF:           return out<<"TYPEDEF";
  case cpp_idt::id_classt::CLASS:             return out<<"CLASS";
  case cpp_idt::id_classt::TEMPLATE:          return out<<"TEMPLATE";
  case cpp_idt::id_classt::TEMPLATE_PARAMETER:return out<<"TEMPLATE_PARAMETER";
  case cpp_idt::id_classt::ROOT_SCOPE:        return out<<"ROOT_SCOPE";
  case cpp_idt::id_classt::BLOCK_SCOPE:       return out<<"BLOCK_SCOPE";
  case cpp_idt::id_classt::TEMPLATE_SCOPE:    return out<<"TEMPLATE_SCOPE";
  case cpp_idt::id_classt::NAMESPACE:         return out<<"NAMESPACE";
  default: return out << "(OTHER)";
  }

  UNREACHABLE;
}
