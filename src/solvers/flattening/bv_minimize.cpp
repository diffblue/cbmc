/*******************************************************************\

Module:

Author: Georg Weissenbacher, georg.weissenbacher@inf.ethz.ch

\*******************************************************************/

#include "bv_minimize.h"

#include <solvers/prop/minimize.h>

void bv_minimizet::add_objective(
  prop_minimizet &prop_minimize,
  const exprt &objective)
{
  // build bit-wise objective function

  const typet &type=objective.type();

  if(type.id()==ID_bool ||
     type.id()==ID_unsignedbv ||
     type.id()==ID_c_enum ||
     type.id()==ID_c_enum_tag ||
     type.id()==ID_signedbv ||
     type.id()==ID_fixedbv)
  {
    // convert it
    bvt bv=boolbv.convert_bv(objective);

    for(std::size_t i=0; i<bv.size(); i++)
    {
      literalt lit=bv[i];

      if(lit.is_constant()) // fixed already, ignore
        continue;

      prop_minimizet::weightt weight=(1LL<<i);

      if(type.id()==ID_signedbv ||
         type.id()==ID_fixedbv ||
         type.id()==ID_floatbv)
      {
        // The top bit is the sign bit, and makes things _smaller_,
        // and thus needs to be maximized.
        if(i==bv.size()-1)
          weight=-weight;
      }

      prop_minimize.objective(lit, weight);
    }
  }
}

void bv_minimizet::operator()(const minimization_listt &symbols)
{
  // build bit-wise objective function

  prop_minimizet prop_minimize(boolbv);
  prop_minimize.set_message_handler(get_message_handler());

  for(minimization_listt::const_iterator
      l_it=symbols.begin();
      l_it!=symbols.end();
      l_it++)
  {
    add_objective(prop_minimize, *l_it);
  }

  // now solve
  prop_minimize();
}
