/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "type.h"

#include <stack>

void typet::copy_to_subtypes(const typet &type)
{
  subtypes().push_back(type);
}

void typet::move_to_subtypes(typet &type)
{
  subtypest &sub=subtypes();
  sub.push_back(static_cast<const typet &>(get_nil_irep()));
  sub.back().swap(type);
}

bool is_number(const typet &type)
{
  const irep_idt &id=type.id();
  return id==ID_rational ||
         id==ID_real ||
         id==ID_integer ||
         id==ID_natural ||
         id==ID_complex ||
         id==ID_unsignedbv ||
         id==ID_signedbv ||
         id==ID_floatbv ||
         id==ID_fixedbv;
}

template <typename Visitee, typename Visitor>
void visit_impl(Visitee &visitee, Visitor &visitor)
{
  std::stack<decltype(&visitee)> stack;
  stack.push(&visitee);

  while(!stack.empty())
  {
    auto &type = *stack.top();
    stack.pop();

    visitor(type);

    for(auto &subtype : type.subtypes())
    {
      stack.push(&subtype);
    }
  }
}

void visit(typet &visitee, type_visitort &visitor)
{
  visit_impl(visitee, visitor);
}

void visit(const typet &visitee, const_type_visitort &visitor)
{
  visit_impl(visitee, visitor);
}
