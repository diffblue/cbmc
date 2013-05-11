/*******************************************************************\

Module: Havoc Loops

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <analyses/natural_loops.h>
#include <analyses/local_may_alias.h>

#include "havoc_loops.h"

class havoc_loopst
{
public:
  typedef goto_functionst::goto_functiont goto_functiont;
  
  explicit havoc_loopst(goto_functiont &goto_function):
    local_may_alias(goto_function),
    natural_loops(goto_function.body)
  {
    havoc_loops();
  }

protected:
  local_may_aliast local_may_alias;
  natural_loops_mutablet natural_loops;
  
  void havoc_loops();
  void havoc_loop(const natural_loops_mutablet::natural_loopt &);

  typedef std::set<exprt> modifiest;
};

/*******************************************************************\

Function: havoc_loopst::havoc_loop

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void havoc_loopst::havoc_loop(const natural_loops_mutablet::natural_loopt &loop)
{
  // first find out what can get changed in the loop
  
  modifiest modifies;
  
  for(natural_loops_mutablet::natural_loopt::const_iterator
      i_it=loop.begin(); i_it!=loop.end(); i_it++)
  {
    const goto_programt::instructiont &instruction=**i_it;

    if(instruction.is_assign())
    {
      const exprt &lhs=to_code_assign(instruction.code).lhs();
      modifiest m=local_may_alias.get(*i_it, lhs);
      modifies.insert(m.begin(), m.end());
    }
    else if(instruction.is_function_call())
    {
      const exprt &lhs=to_code_function_call(instruction.code).lhs();
      modifiest m=local_may_alias.get(*i_it, lhs);
      modifies.insert(m.begin(), m.end());
    }
  }
  
  // now havoc on all backwards gotos

  for(natural_loops_mutablet::natural_loopt::const_iterator
      i_it=loop.begin(); i_it!=loop.end(); i_it++)
  {
    const goto_programt::instructiont &instruction=**i_it;
    if(instruction.is_backwards_goto())
    {
      

    }    
  }
}

/*******************************************************************\

Function: havoc_loopst::havoc_loops

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void havoc_loopst::havoc_loops()
{
  // iterate over the (natural) loops
  
  for(natural_loops_mutablet::loop_mapt::const_iterator
      l_it=natural_loops.loop_map.begin();
      l_it!=natural_loops.loop_map.end();
      l_it++)
    havoc_loop(l_it->second);
}

/*******************************************************************\

Function: havoc_loops

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void havoc_loops(goto_functionst &goto_functions)
{
  Forall_goto_functions(it, goto_functions)
    havoc_loopst(it->second);
}
