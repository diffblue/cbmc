/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "functions.h"

#include <util/std_types.h>
#include <util/std_expr.h>

void functionst::record(
  const function_application_exprt &function_application)
{
  function_map[function_application.function()].applications.
    insert(function_application);
}

void functionst::add_function_constraints()
{
  for(function_mapt::const_iterator it=
      function_map.begin();
      it!=function_map.end();
      it++)
    add_function_constraints(it->second);
}

exprt functionst::arguments_equal(const exprt::operandst &o1,
                                  const exprt::operandst &o2)
{
  PRECONDITION(o1.size() == o2.size());

  exprt::operandst conjuncts;
  conjuncts.reserve(o1.size());

  for(std::size_t i=0; i<o1.size(); i++)
  {
    exprt lhs=o1[i];
    exprt rhs = typecast_exprt::conditional_cast(o2[i], o1[i].type());
    conjuncts.push_back(equal_exprt(lhs, rhs));
  }

  return conjunction(conjuncts);
}

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
