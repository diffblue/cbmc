/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "prop_conv_store.h"

void prop_conv_storet::set_to(const exprt &expr, bool value)
{
  constraintt &constraint=constraints.add_constraint();
  constraint.type=constraintt::typet::SET_TO;
  constraint.expr=expr;
  constraint.value=value;
}

literalt prop_conv_storet::convert(const exprt &expr)
{
  constraintt &constraint=constraints.add_constraint();
  constraint.type=constraintt::typet::CONVERT;
  constraint.expr=expr;
  #if 0
  constraint.literal=prop.new_variable();
  #endif
  return constraint.literal;
}

void prop_conv_storet::constraintst::replay(prop_convt &dest) const
{
  for(constraint_listt::const_iterator
      it=constraint_list.begin();
      it!=constraint_list.end();
      it++)
    it->replay(dest);
}

void prop_conv_storet::constraintst::print(std::ostream &out) const
{
  for(constraint_listt::const_iterator
      it=constraint_list.begin();
      it!=constraint_list.end();
      it++)
    it->print(out);
}

void prop_conv_storet::constraintt::replay(prop_convt &dest) const
{
  switch(type)
  {
  case typet::SET_TO:
    dest.set_to(expr, value);
    break;

  case typet::CONVERT:
    // dest.prop.set_equal(dest.convert_rest(expr), literal);
    break;

  default:
    assert(false);
  }
}

void prop_conv_storet::constraintt::print(std::ostream &out) const
{
  switch(type)
  {
  case typet::SET_TO:
    out << "SET_TO " << (value?"TRUE":"FALSE") << ": ";
    out << expr.pretty() << "\n";
    break;

  case typet::CONVERT:
    out << "CONVERT(" << literal.dimacs() << "): ";
    out << expr.pretty() << "\n";
    break;

  default:
    assert(false);
  }
}
