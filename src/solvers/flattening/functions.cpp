/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#include <cassert>

#include <util/std_types.h>
#include <util/std_expr.h>

#include "functions.h"

/*******************************************************************\

Function: functionst::record

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void functionst::record(
  const function_application_exprt &function_application)
{
  function_map[function_application.function()].applications.
    insert(function_application);
}

/*******************************************************************\

Function: functionst::add_function_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void functionst::add_function_constraints()
{
  for(function_mapt::const_iterator it=
      function_map.begin();
      it!=function_map.end();
      it++)
    add_function_constraints(it->second);
}

/*******************************************************************\

Function: functionst::add_function_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt functionst::arguments_equal(const exprt::operandst &o1,
                                  const exprt::operandst &o2)
{
  assert(o1.size()==o2.size());
  
  if(o1.empty())
    return true_exprt();

  and_exprt and_expr;
  and_exprt::operandst &conjuncts=and_expr.operands();
  conjuncts.resize(o1.size());
  
  for(unsigned i=0; i<o1.size(); i++)
  {
    exprt lhs=o1[i];
    exprt rhs=o2[i];

    if(lhs.type()!=rhs.type())
      rhs.make_typecast(lhs.type());
      
    conjuncts[i]=equal_exprt(lhs, rhs);
  }

  return and_expr;
}

/*******************************************************************\

Function: functionst::add_function_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void functionst::add_function_constraints(const function_infot &info)
{
  // Do Ackermann's function reduction.
  // This is quadratic, slow, and needs to be modernized.

  for(std::set<function_application_exprt>::const_iterator
      it1=info.applications.begin();
      it1!=info.applications.end();
      it1++)
  {
    for(std::set<function_application_exprt>::const_iterator
        it2=info.applications.begin();
        it2!=it1;
        it2++)
    {
      exprt arguments_equal_expr=
        arguments_equal(it1->arguments(), it2->arguments());

      implies_exprt implication(arguments_equal_expr,
                                equal_exprt(*it1, *it2));
      
      prop_conv.set_to_true(implication);
    }
  }
}
