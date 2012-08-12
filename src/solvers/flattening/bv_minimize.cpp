/*******************************************************************\

Module:

Author: Georg Weissenbacher, georg.weissenbacher@inf.ethz.ch

\*******************************************************************/

#include <cassert>

#include <solvers/prop/minimize.h>

#include "bv_minimize.h"

/*******************************************************************\

Function: bv_minimizet::add_objective

  Inputs: 

 Outputs:

 Purpose: 

\*******************************************************************/

void bv_minimizet::add_objective(
  prop_minimizet &prop_minimize,
  const exprt &objective)
{
  // build bit-wise objective function

  const typet &type=objective.type();

  if(type.id()==ID_bool ||
     type.id()==ID_unsignedbv ||
     type.id()==ID_c_enum ||
     type.id()==ID_signedbv ||
     type.id()==ID_fixedbv)
  {    
    unsigned width=boolbv.boolbv_width(type);
  
    for(unsigned i=0; i<width; i++)
    {
      literalt lit;
  
      if(boolbv.literal(objective, i, lit))
        continue; // there's no corresponding literal, ignore
      
      if(lit.is_constant()) // fixed already, ignore
        continue;

      prop_minimizet::weightt weight=(1LL<<i);
      
      if(type.id()==ID_signedbv || type.id()==ID_fixedbv)
      {
        if(absolute_value)
        {
          // need to minimize sign XOR bit
          if(i!=width-1)
          {
            literalt sign;
            boolbv.literal(objective, width-1, sign);
            lit=boolbv.prop.lxor(sign, lit);
          }
        }
        else
        {
          // The top bit makes things _smaller_, and thus needs
          // to be maximized.
          if(i==width-1)
            weight=-weight;
        }
      }
      
      prop_minimize.objective(lit, weight);
    }
  }
}

/*******************************************************************\

Function: bv_minimizet::operator()

  Inputs: 

 Outputs:

 Purpose: 

\*******************************************************************/

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
