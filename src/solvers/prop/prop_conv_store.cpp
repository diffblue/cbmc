/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "prop_conv_store.h"

/*******************************************************************\

Function: prop_conv_storet::set_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_conv_storet::set_to(const exprt &expr, bool value)
{
  constraintt &constraint=constraints.add_constraint();
  constraint.type=constraintt::SET_TO;
  constraint.expr=expr;
  constraint.value=value;
}

/*******************************************************************\

Function: prop_conv_storet::convert_rest

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt prop_conv_storet::convert(const exprt &expr)
{
  constraintt &constraint=constraints.add_constraint();
  constraint.type=constraintt::CONVERT;
  constraint.expr=expr;
  #if 0
  constraint.literal=prop.new_variable();
  #endif
  return constraint.literal;
}

/*******************************************************************\

Function: prop_conv_storet::constraintst::replay

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_conv_storet::constraintst::replay(prop_convt &dest) const
{
  for(constraint_listt::const_iterator
      it=constraint_list.begin();
      it!=constraint_list.end();
      it++)
    it->replay(dest);
}

/*******************************************************************\

Function: prop_conv_storet::constraintst::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_conv_storet::constraintst::print(std::ostream &out) const
{
  for(constraint_listt::const_iterator
      it=constraint_list.begin();
      it!=constraint_list.end();
      it++)
    it->print(out);
}

/*******************************************************************\

Function: prop_conv_storet::constraintt::replay

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_conv_storet::constraintt::replay(prop_convt &dest) const
{
  switch(type)
  {
  case SET_TO:
    dest.set_to(expr, value);
    break;
  
  case CONVERT:
    //dest.prop.set_equal(dest.convert_rest(expr), literal);
    break;

  default:
    assert(false);
  }
}

/*******************************************************************\

Function: prop_conv_storet::constraintt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_conv_storet::constraintt::print(std::ostream &out) const
{
  switch(type)
  {
  case SET_TO:
    out << "SET_TO " << (value?"TRUE":"FALSE") << ": ";
    out << expr << "\n";
    break;
  
  case CONVERT:
    out << "CONVERT(" << literal.dimacs() << "): ";
    out << expr << "\n";
    break;
  
  default:
    assert(false);
  }
}

