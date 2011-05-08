/*******************************************************************\

Module: Set Claims

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <i2string.h>
#include <hash_cont.h>

#include "set_claims.h"

/*******************************************************************\

Function: set_claims

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void set_claims(
  goto_programt &goto_program,
  std::map<irep_idt, unsigned> &claim_counters,
  hash_set_cont<std::string, string_hash> &claim_set)
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
    
    hash_set_cont<std::string, string_hash>::iterator
      c_it=claim_set.find(claim_name);
      
    if(c_it==claim_set.end())
      it->type=SKIP;
    else
      claim_set.erase(c_it);
  }
}

/*******************************************************************\

Function: set_claims

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void set_claims(
  goto_programt &goto_program,
  const std::list<std::string> &claims)
{
  hash_set_cont<std::string, string_hash> claim_set;
  std::map<irep_idt, unsigned> claim_counters;
  
  for(std::list<std::string>::const_iterator
      it=claims.begin();
      it!=claims.end();
      it++)
    claim_set.insert(*it);

  set_claims(goto_program, claim_counters, claim_set);
  
  if(!claim_set.empty())
    throw "claim "+(*claim_set.begin())+" not found";
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
  hash_set_cont<std::string, string_hash> claim_set;
  std::map<irep_idt, unsigned> claim_counters;

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
      set_claims(it->second.body, claim_counters, claim_set);

  if(!claim_set.empty())
    throw "claim "+(*claim_set.begin())+" not found";
}
