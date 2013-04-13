/*******************************************************************\

Module: Unused function removal

Author: CM Wintersteiger

\*******************************************************************/

#include <util/message_stream.h>

#include "remove_unused_functions.h"

/*******************************************************************\

Function: remove_unused_functions

  Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/

void remove_unused_functions(
  goto_functionst &functions,
  message_handlert &message_handler)
{
  std::set<irep_idt> used_functions;
  std::list<goto_functionst::function_mapt::iterator> unused_functions;
  find_used_functions(ID_main, functions, used_functions);
    
  for(goto_functionst::function_mapt::iterator it=
        functions.function_map.begin();
      it!=functions.function_map.end();
      it++)
  {
    if(used_functions.find(it->first)==used_functions.end())
      unused_functions.push_back(it);
  }
  
  message_streamt message_stream(message_handler);
  
  if(unused_functions.size()>0)
  {
    message_stream.str
      << "Dropping " << unused_functions.size() << " of " <<
      functions.function_map.size() << " functions (" << 
      used_functions.size() << " used)";
  }

  message_stream.statistics();
  
  for(std::list<goto_functionst::function_mapt::iterator>::const_iterator 
        it=unused_functions.begin();
      it!=unused_functions.end();
      it++)
    functions.function_map.erase(*it); 
}

/*******************************************************************\

Function: find_used_functions

  Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/

void find_used_functions(
  const irep_idt &start,
  goto_functionst &functions,
  std::set<irep_idt> &seen)
{
  std::pair<std::set<irep_idt>::const_iterator, bool> res =
    seen.insert(start);
  
  if(!res.second) 
    return;
  else
  {
    goto_functionst::function_mapt::const_iterator f_it =
      functions.function_map.find(start);
    
    if(f_it!=functions.function_map.end())
    {
      forall_goto_program_instructions(it, f_it->second.body){      
        if(it->type==FUNCTION_CALL)
        {
          const code_function_callt &call = 
            to_code_function_call(to_code(it->code));
          
          // check that this is actually a simple call
          assert(call.function().id()==ID_symbol);
          
          find_used_functions(call.function().get(ID_identifier), 
                              functions, 
                              seen);
        }
      }
    }
  }
}
