/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <arith_tools.h>
#include <replace_expr.h>

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_quantifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolbvt::convert_quantifier(const exprt &expr)
{
  if(expr.operands().size()!=3)
    return SUB::convert_rest(expr);
  
  literalt l=prop.new_variable();
  
  quantifier_list.push_back(quantifiert());
  quantifier_list.back().l=l;
  quantifier_list.back().expr=expr;
  
  return l;
}

/*******************************************************************\

Function: boolbvt::post_process_quantifiers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::post_process_quantifiers()
{
  std::set<exprt> instances;
  
  if(quantifier_list.empty()) return;
  
  for(quantifier_listt::const_iterator q_it=quantifier_list.begin();
      q_it!=quantifier_list.end();
      q_it++)
    forall_operands(o_it, q_it->expr.op1())
      instances.insert(*o_it);

  if(instances.empty())
    throw "post_process_quantifiers: no instances";

  for(quantifier_listt::const_iterator q_it=quantifier_list.begin();
      q_it!=quantifier_list.end();
      q_it++)
  {
    const exprt &expr=q_it->expr;
    
    bvt inst_bv;
    inst_bv.reserve(instances.size());
    
    for(std::set<exprt>::const_iterator it=instances.begin();
        it!=instances.end();
        it++)
    {
      exprt dest(expr.op2());

      exprt by(*it);
      if(expr.op0().type()!=by.type())
        by.make_typecast(expr.op0().type());

      replace_expr(expr.op0(), by, dest);
      inst_bv.push_back(convert(dest));
    }

    if(expr.id()=="forall")
      prop.set_equal(prop.land(inst_bv), q_it->l);
    else if(expr.id()=="exists")
      prop.set_equal(prop.lor(inst_bv), q_it->l);
    else
      assert(false);
  }
}
