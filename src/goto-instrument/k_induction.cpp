/*******************************************************************\

Module: k-induction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>

#include <analyses/natural_loops.h>
#include <analyses/local_may_alias.h>

#include <goto-programs/remove_skip.h>

#include "unwind.h"
#include "k_induction.h"

class k_inductiont
{
public:
  typedef goto_functionst::goto_functiont goto_functiont;
  
  k_inductiont(
    goto_functiont &_goto_function,
    unsigned _k,
    bool _base_case, bool _step_case):
    goto_function(_goto_function),
    local_may_alias(_goto_function),
    natural_loops(_goto_function.body),
    k(_k), base_case(_base_case), step_case(_step_case)
  {
    k_induction();
  }

protected:
  goto_functiont &goto_function;
  local_may_aliast local_may_alias;
  natural_loops_mutablet natural_loops;
  
  const unsigned k;
  const bool base_case, step_case;
  
  typedef std::set<exprt> modifiest;
  typedef const natural_loops_mutablet::natural_loopt loopt;

  void k_induction();

  void process_loop(
    const goto_programt::targett loop_head,
    const loopt &);

  void build_havoc_code(
    const goto_programt::targett loop_head,
    const modifiest &modifies,
    goto_programt &dest);
  
  void get_modifies(const loopt &, modifiest &);
  void get_modifies_lhs(
    goto_programt::const_targett,
    const exprt &lhs,
    modifiest &modifies);
  
  goto_programt::targett get_loop_exit(const loopt &);
};

/*******************************************************************\

Function: k_inductiont::get_loop_exit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

goto_programt::targett k_inductiont::get_loop_exit(const loopt &loop)
{
  assert(!loop.empty());

  // find the last instruction in the loop
  std::map<unsigned, goto_programt::targett> loop_map;
  
  for(loopt::const_iterator l_it=loop.begin();
      l_it!=loop.end();
      l_it++)
    loop_map[(*l_it)->location_number]=*l_it;

  // get the one with the highest number
  goto_programt::targett last=(--loop_map.end())->second;
  
  return ++last;
}

/*******************************************************************\

Function: k_inductiont::build_havoc_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void k_inductiont::build_havoc_code(
  const goto_programt::targett loop_head,
  const modifiest &modifies,
  goto_programt &dest)
{
  for(modifiest::const_iterator
      m_it=modifies.begin();
      m_it!=modifies.end();
      m_it++)
  {
    exprt lhs=*m_it;
    exprt rhs=side_effect_expr_nondett(lhs.type());
  
    goto_programt::targett t=dest.add_instruction(ASSIGN);
    t->function=loop_head->function;
    t->location=loop_head->location;
    t->code=code_assignt(lhs, rhs);
    t->code.location()=loop_head->location;
  }
}

/*******************************************************************\

Function: k_inductiont::process_loop

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void k_inductiont::process_loop(
  const goto_programt::targett loop_head,
  const loopt &loop)
{
  assert(!loop.empty());

  // compute the loop exit
  goto_programt::targett loop_exit=
    get_loop_exit(loop);

  if(base_case)
  {
    // now unwind k times
    unwind(goto_function.body, loop_head, loop_exit, k);
  }

  if(step_case)
  {
    // step case

    // first unwind to get k+1 copies
    std::vector<goto_programt::targett> exit_points;
    unwind(goto_function.body, loop_head, loop_exit, k, exit_points);

    // find out what can get changed in the loop  
    modifiest modifies;
    get_modifies(loop, modifies);
    
    // build the havoc-ing code
    goto_programt havoc_code;
    build_havoc_code(loop_head, modifies, havoc_code);
    
    // Now havoc at the loop head. Use insert_swap to
    // preserve jumps to loop head.
    goto_function.body.insert_before_swap(loop_head, havoc_code);
    
    // now turn any assertions in iterations 0..k-1 into assumptions
    assert(exit_points.size()==k+1);
    goto_programt::targett start=loop_head;
    for(unsigned i=0; i<k; i++)
    {
      goto_programt::targett end=exit_points[i];
      for(goto_programt::targett t=start; t!=end; t++)
      {
        assert(t!=goto_function.body.instructions.end());
        if(t->is_assert()) t->type=ASSERT;
      }
      start=end;
    }
  }

  // remove skips
  remove_skip(goto_function.body);
}

/*******************************************************************\

Function: k_inductiont::get_modifies_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void k_inductiont::get_modifies_lhs(
  goto_programt::const_targett t,
  const exprt &lhs,
  modifiest &modifies)
{
  if(lhs.id()==ID_symbol)
    modifies.insert(lhs);
  else if(lhs.id()==ID_dereference)
  {
    modifiest m=local_may_alias.get(t, to_dereference_expr(lhs).pointer());
    for(modifiest::const_iterator m_it=m.begin();
        m_it!=m.end(); m_it++)
      get_modifies_lhs(t, *m_it, modifies);
  }
  else if(lhs.id()==ID_member)
  {
  }
  else if(lhs.id()==ID_index)
  {
  }
  else if(lhs.id()==ID_if)
  {
    get_modifies_lhs(t, to_if_expr(lhs).true_case(), modifies);
    get_modifies_lhs(t, to_if_expr(lhs).false_case(), modifies);
  }
}

/*******************************************************************\

Function: k_inductiont::get_modifies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void k_inductiont::get_modifies(
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
      get_modifies_lhs(*i_it, lhs, modifies);
    }
    else if(instruction.is_function_call())
    {
      const exprt &lhs=to_code_function_call(instruction.code).lhs();
      get_modifies_lhs(*i_it, lhs, modifies);
    }
  }
}

/*******************************************************************\

Function: k_inductiont::k_induction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void k_inductiont::k_induction()
{
  // iterate over the (natural) loops in the function
  
  for(natural_loops_mutablet::loop_mapt::const_iterator
      l_it=natural_loops.loop_map.begin();
      l_it!=natural_loops.loop_map.end();
      l_it++)
    process_loop(l_it->first, l_it->second);
}

/*******************************************************************\

Function: k_induction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void k_induction(
  goto_functionst &goto_functions,
  unsigned k,
  bool base_case, bool step_case)
{
  Forall_goto_functions(it, goto_functions)
    k_inductiont(it->second, k, base_case, step_case);
}
