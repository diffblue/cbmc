/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/arith_tools.h>
#include <util/i2string.h>
#include <util/ieee_float.h>

#include "heap_dec.h"

#include "heaptransformer.h"
#include "heapabstraction.h"
#include "heapheuristics.h"
#include "heaprefine.h"

/*******************************************************************\

Function: heap_dect::decision_procedure_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string heap_dect::decision_procedure_text() const
{
  return "hippo";
}

/*******************************************************************\

Function: heap_dect::dec_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool have_eq(heapabs sol, std::string id1, std::string id2) 
{
  heapvar v(id1);
  heaplit* l = new eq_lit(heapvar(id1),heapexpr(id2),stateTrue);
  if(sol.entails_literal(l))
  {

#if 0
    std::cout << "have " << *l << std::endl;
#endif
    return true;
  }
#if 0
  std::cout << "do not have " << *l << std::endl;
#endif
  return false;
}

bool have_sel(heapabs sol, std::string id1, std::string id2, std::string heap_id, std::string field) 
{
  heapvar v(id1);
  heaplit* l = new eq_lit(heapvar(id1),heapexpr(id2,heap_id,field),stateTrue);
  if(sol.entails_literal(l))
  {

#if 0
    std::cout << "have " << *l << std::endl;
#endif
    return true;
  }
#if 0
  std::cout << "do not have " << *l << std::endl;
#endif

  return false;
}

decision_proceduret::resultt heap_dect::dec_solve()
{
  //call hippo
  heaprefine<heapabs, heaptrans, heapheuristics> solver;
  heapabs sol;
  heapheuristics h;

  std::cout << "Number of clauses: " << formula.size() << std::endl;

  heaptrans t(formula);

  transformerRefinementResult::s ret = solver.solve(sol, t, h);

  if(ret==transformerRefinementResult::NotBottom)
  {
    boolean_assignment.clear();
    boolean_assignment.resize(no_boolean_variables, false);

/*    
    typedef hash_map_cont<std::string, std::string, string_hash> valuest;
    valuest values;

    while(std::getline(in, line))
    {
      std::size_t pos=line.find(' ');
      if(pos!=std::string::npos)
        values[std::string(line, 0, pos)]=
          std::string(line, pos+1, std::string::npos);
    }
*/

    // Theory variables

    /*
    for(unsigned i=0;i<=6;i++) 
      for(unsigned j=0;j<=6;j++) 
        if(i!=j) have_eq(sol,"|heap"+i2string(i)+"|","|heap"+i2string(j)+"|");

    for(unsigned i=0;i<=6;i++) 
      have_sel(sol,"|c::main::1::one!0@1#1|","|c::main::1::p!0@1#3|","|heap"+i2string(i)+"|","|h|");
    */

    for(identifier_mapt::iterator
        it=identifier_map.begin();
        it!=identifier_map.end();
        it++)
    {
      if(it->second.type.id()==ID_pointer || it->second.type.id()==ID_struct) 
      {
        it->second.value.make_nil();
        std::string id = convert_identifier(it->first);
        if(have_eq(sol,id,"NULL")) 
	{
	  pointer_typet type = (it->second.type.id()==ID_pointer) ? 
            to_pointer_type(ns.follow(it->second.type)) : pointer_typet(ns.follow(it->second.type));
          it->second.value = null_pointer_exprt(type);
          continue;
        }
	for(identifier_mapt::iterator
	      it2=identifier_map.begin();
	    it2!=identifier_map.end();
	    it2++)
	{
	  if((it2->second.type.id()==ID_pointer || it2->second.type.id()==ID_struct) &&
             it2->first!=it->first)
	   { 
             std::string id2 = convert_identifier(it2->first);
	     if(have_eq(sol,id,id2)) 
	       {
		 //		 pointer_typet type = to_pointer_type(ns.follow(it->second.type));
		 it->second.value = symbol_exprt(it2->first);
		 continue;
	       }
	   }
	}
      }
      else if(it->second.type.id()==ID_bool) 
      {
        it->second.value.make_nil();
        literalt& l = symbols[it->first];
        if(heap_literal_map.find(l.var_no())==heap_literal_map.end()) continue;
        heaplit* hl = heap_literal_map[l.var_no()];
        if(sol.entails_literal(hl)) {
#if 0
          status() << "have " << it->first << "==" << (hl->state==stateTrue) << eom;
#endif

          if(hl->state==stateTrue)
            it->second.value = true_exprt(); 
          else
            it->second.value =  false_exprt();
        }
        else {
          hl->complement();
          if(sol.entails_literal(hl)) {
#if 0
            status() << "have " << it->first << "==" << (hl->state==stateTrue) << eom;
#endif

            if(hl->state==stateTrue)
              it->second.value = true_exprt(); 
            else
              it->second.value =  false_exprt();
	  }
        }
      }
    }

    // Booleans
   
    for(unsigned v=0; v<no_boolean_variables; v++)
    {
      if(heap_literal_map.find(v)==heap_literal_map.end()) continue;
      heaplit* l = heap_literal_map[v];
      bool value = !(l->state==stateTrue);
      if(sol.entails_literal(l)) value = true;
      boolean_assignment[v] = value;
    }

    return D_SATISFIABLE;
  }
  else if(ret==transformerRefinementResult::Bottom)
  {
    return D_UNSATISFIABLE;
  }

  assert(false);
}

