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
  
  explicit havoc_loopst(goto_functiont &_goto_function):
    goto_function(_goto_function),
    local_may_alias(_goto_function),
    natural_loops(_goto_function.body)
  {
    havoc_loops();
  }

protected:
  goto_functiont &goto_function;
  local_may_aliast local_may_alias;
  natural_loops_mutablet natural_loops;
  
  typedef std::set<exprt> modifiest;
  typedef const natural_loops_mutablet::natural_loopt loopt;

  void havoc_loops();

  void havoc_loop(
    const goto_programt::targett loop_head,
    const loopt &);

  void build_havoc_code(
    const goto_programt::targett loop_head,
    const modifiest &modifies,
    goto_programt &dest);
  
  void get_modifies(const loopt &, modifiest &);

  goto_programt::targett get_loop_exit(const loopt &);
};

/*******************************************************************\

Function: havoc_loopst::get_loop_exit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

goto_programt::targett havoc_loopst::get_loop_exit(const loopt &loop)
{
  assert(!loop.empty());
  return *loop.begin();
}

/*******************************************************************\

Function: havoc_loopst::build_havoc_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void havoc_loopst::build_havoc_code(
  const goto_programt::targett loop_head,
  const modifiest &modifies,
  goto_programt &dest)
{
  for(modifiest::const_iterator
      m_it=modifies.begin();
      m_it!=modifies.end();
      m_it++)
  {
  }
}

/*******************************************************************\

Function: havoc_loopst::havoc_loop

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void havoc_loopst::havoc_loop(
  const goto_programt::targett loop_head,
  const loopt &loop)
{
  assert(!loop.empty());

  // first find out what can get changed in the loop  
  modifiest modifies;
  get_modifies(loop, modifies);
  
  // build the havoc-ing code
  goto_programt havoc_code;
  build_havoc_code(loop_head, modifies, havoc_code);
  
  // Now havoc at the loop head. Use insert_swap to
  // preserve jumps to loop head.
  goto_function.body.insert_before_swap(loop_head, havoc_code);
  
  // compute the loop exit
  goto_programt::targett loop_exit=
    get_loop_exit(loop);

  // divert all gotos to the loop head to the loop exit
  for(loopt::const_iterator
      i_it=loop.begin(); i_it!=loop.end(); i_it++)
  {
    goto_programt::instructiont &instruction=**i_it;
    if(instruction.is_goto())
    {
      for(goto_programt::targetst::iterator
          t_it=instruction.targets.begin();
          t_it!=instruction.targets.end();
          t_it++)
      {
        if(*t_it==loop_head)
          *t_it=loop_exit; // divert
      }
    }
  }
}

/*******************************************************************\

Function: havoc_loopst::get_modifies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void havoc_loopst::get_modifies(
  const loopt &loop,
  modifiest &modifies)
{
  for(loopt::const_iterator
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
}

/*******************************************************************\

Function: havoc_loopst::havoc_loops

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void havoc_loopst::havoc_loops()
{
  // iterate over the (natural) loops in the function
  
  for(natural_loops_mutablet::loop_mapt::const_iterator
      l_it=natural_loops.loop_map.begin();
      l_it!=natural_loops.loop_map.end();
      l_it++)
    havoc_loop(l_it->first, l_it->second);
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
