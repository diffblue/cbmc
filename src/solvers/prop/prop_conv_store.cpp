/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

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

literalt prop_conv_storet::convert_rest(const exprt &expr)
{
  constraintt &constraint=constraints.add_constraint();
  constraint.type=constraintt::CONVERT_REST;
  constraint.expr=expr;
  constraint.literal=prop.new_variable();
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

Function: prop_conv_store_constraintt::replay

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_conv_store_constraintt::replay(prop_convt &dest) const
{
  switch(type)
  {
  case SET_TO:
    dest.set_to(expr, value);
    break;
  
  case CONVERT_REST:
    dest.prop.set_equal(dest.convert_rest(expr), literal);
    break;
  
  default:
    assert(false);
  }
}

/*******************************************************************\

Function: prop_conv_store_constraintt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_conv_store_constraintt::print(std::ostream &out) const
{
  switch(type)
  {
  case SET_TO:
    out << "SET_TO " << (value?"TRUE":"FALSE") << ": ";
    out << expr << std::endl;
    break;
  
  case CONVERT_REST:
    out << "CONVERT(" << literal.dimacs() << "): ";
    out << expr << std::endl;
    break;
  
  default:
    assert(false);
  }
}

