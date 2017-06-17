/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <ostream>

#include "cpp_id.h"
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
    for(cpp_id_mapt::const_iterator it=sub.begin();
        it!=sub.end();
        it++)
      it->second.print(out, indent+2);

    out << '\n';
  }
}

void cpp_idt::print_fields(std::ostream &out, unsigned indent) const
{
  for(unsigned i=0; i<indent; i++) out << ' ';
  out << "**identifier=" << identifier << '\n';

  for(unsigned i=0; i<indent; i++) out << ' ';
  out << "  prefix=" << prefix << '\n';

  for(unsigned i=0; i<indent; i++) out << ' ';
  out << "  suffix=" << suffix << '\n';

  for(unsigned i=0; i<indent; i++) out << ' ';
  out << "  base_name=" << base_name << '\n';

  for(unsigned i=0; i<indent; i++) out << ' ';
  out << "  method=" << is_method << '\n';

  for(unsigned i=0; i<indent; i++) out << ' ';
  out << "  class_identifier=" << class_identifier << '\n';

  for(scope_listt::const_iterator
      it=secondary_scopes.begin();
      it!=secondary_scopes.end();
      it++)
  {
    for(unsigned i=0; i<indent; i++) out << ' ';
    out << "  secondary_scope=" << (*it)->identifier << '\n';
  }

  for(scope_listt::const_iterator
      it=using_scopes.begin();
      it!=using_scopes.end();
      it++)
  {
    for(unsigned i=0; i<indent; i++) out << ' ';
    out << "  using_scope=" << (*it)->identifier << '\n';
  }

  for(unsigned i=0; i<indent; i++) out << ' ';
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

  for(unsigned i=0; i<indent; i++) out << ' ';
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
}
