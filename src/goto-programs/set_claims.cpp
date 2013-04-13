/*******************************************************************\

Module: Set Claims

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/i2string.h>
#include <util/hash_cont.h>

#include "set_claims.h"

/*******************************************************************\

Function: set_claims

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void set_claims(
  goto_programt &goto_program,
  hash_set_cont<irep_idt, irep_id_hash> &claim_set)
{
  for(goto_programt::instructionst::iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {
    if(!it->is_assert()) continue;
    
    irep_idt claim_name=it->location.get_claim();

    hash_set_cont<irep_idt, irep_id_hash>::iterator
      c_it=claim_set.find(claim_name);
      
    if(c_it==claim_set.end())
      it->type=SKIP;
    else
      claim_set.erase(c_it);
  }
}

/*******************************************************************\

Function: label_claims

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void label_claims(
  goto_programt &goto_program,
  std::map<irep_idt, unsigned> &claim_counters)
{
  for(goto_programt::instructionst::iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {
    if(!it->is_assert()) continue;
    
    irep_idt function=it->location.get_function();
    unsigned &count=claim_counters[function];
    
    count++;
    
    std::string claim_name=
      function==""?i2string(count):
      id2string(function)+"."+i2string(count);
    
    it->location.set_claim(claim_name);
  }
}

/*******************************************************************\

Function: set_claims

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void set_claims(
  goto_functionst &goto_functions,
  const std::list<std::string> &claims)
{
  hash_set_cont<irep_idt, irep_id_hash> claim_set;

  for(std::list<std::string>::const_iterator
      it=claims.begin();
      it!=claims.end();
      it++)
    claim_set.insert(*it);

  for(goto_functionst::function_mapt::iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    if(!it->second.is_inlined())
      set_claims(it->second.body, claim_set);

  if(!claim_set.empty())
    throw "claim "+id2string(*claim_set.begin())+" not found";
}

/*******************************************************************\

Function: label_claims

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void label_claims(goto_functionst &goto_functions)
{
  std::map<irep_idt, unsigned> claim_counters;

  for(goto_functionst::function_mapt::iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    if(!it->second.is_inlined())
      label_claims(it->second.body, claim_counters);
}

/*******************************************************************\

Function: make_assertions_false

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void make_assertions_false(
  goto_functionst &goto_functions)
{
  for(goto_functionst::function_mapt::iterator
      f_it=goto_functions.function_map.begin();
      f_it!=goto_functions.function_map.end();
      f_it++)
  {
    goto_programt &goto_program=f_it->second.body;
    
    for(goto_programt::instructionst::iterator
        i_it=goto_program.instructions.begin();
        i_it!=goto_program.instructions.end();
        i_it++)
    {
      if(!i_it->is_assert()) continue;
      i_it->guard.make_false();
    }
  }
}

