/*******************************************************************\

Module: loop unwinding

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>

#include "unwind.h"

/*******************************************************************\

Function: unwind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind(
  goto_programt &goto_program,
  goto_programt::targett loop_head,
  goto_programt::targett loop_exit,
  const unsigned k)
{
  std::vector<goto_programt::targett> exit_points;
  unwind(goto_program, loop_head, loop_exit, k, exit_points);
}

/*******************************************************************\

Function: unwind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind(
  goto_programt &goto_program,
  goto_programt::targett loop_head,
  goto_programt::targett loop_exit,
  const unsigned k,
  std::vector<goto_programt::targett> &iteration_points)
{
  assert(k!=0);
  
  iteration_points.resize(k);

  // loop_exit: where to go after the loop ends
  // loop_iter: where to go for the next iteration
  
  // Add a 'goto' and a 'skip' _before_ loop_exit.
  // The goto is to take care of 'fall-out' loop exit, and is
  // not needed if there is an unconditional goto before loop_exit.

  if(loop_exit!=goto_program.instructions.begin())
  {  
    goto_programt::targett t_before=loop_exit;
    t_before--;
    
    if(t_before->is_goto() && t_before->guard.is_true())
    {
      // no 'fall-out'
    }
    else
    {
      // guard against 'fall-out'
      goto_programt::targett t_goto=goto_program.insert_before(loop_exit);
  
      t_goto->make_goto(loop_exit);
      t_goto->location=loop_exit->location;
      t_goto->function=loop_exit->function;
      t_goto->guard=true_exprt();
    }
  }
  
  goto_programt::targett t_skip=goto_program.insert_before(loop_exit);
  goto_programt::targett loop_iter=t_skip;
  
  t_skip->make_skip();
  t_skip->location=loop_head->location;
  t_skip->function=loop_head->function;
  
  // record the exit point of first iteration
  iteration_points[0]=loop_iter;
  
  // build a map for branch targets inside the loop
  std::map<goto_programt::targett, unsigned> target_map;

  { 
    unsigned count=0;
    for(goto_programt::targett t=loop_head;
        t!=loop_exit; t++, count++)
    {
      assert(t!=goto_program.instructions.end());
      target_map[t]=count;
    }
  }

  // re-direct any branches that go to loop_head to loop_iter
  
  for(goto_programt::targett t=loop_head;
      t!=loop_iter; t++)
  {
    assert(t!=goto_program.instructions.end());
    for(goto_programt::instructiont::targetst::iterator
        t_it=t->targets.begin();
        t_it!=t->targets.end();
        t_it++)
      if(*t_it==loop_head) *t_it=loop_iter;
  }
  
  // we make k-1 copies, to be inserted before loop_exit
  goto_programt copies;

  for(unsigned i=1; i<k; i++)
  {
    // make a copy
    std::vector<goto_programt::targett> target_vector;
    target_vector.reserve(target_map.size());

    for(goto_programt::targett t=loop_head;
        t!=loop_exit; t++)
    {
      assert(t!=goto_program.instructions.end());
      goto_programt::targett copied_t=copies.add_instruction();
      *copied_t=*t;
      target_vector.push_back(copied_t);
    }

    // record exit point of this copy
    iteration_points[i]=target_vector.back();
    
    // adjust the intra-loop branches

    for(unsigned i=0; i<target_vector.size(); i++)
    {
      goto_programt::targett t=target_vector[i];

      for(goto_programt::instructiont::targetst::iterator
          t_it=t->targets.begin();
          t_it!=t->targets.end();
          t_it++)
      {
        std::map<goto_programt::targett, unsigned>::const_iterator
          m_it=target_map.find(*t_it);
        if(m_it!=target_map.end()) // intra-loop?
        {
          assert(m_it->second<target_vector.size());
          *t_it=target_vector[m_it->second];
        }
      }
    }
  }  
  
  assert(copies.instructions.size()==(k-1)*target_map.size());
  
  // now insert copies before loop_exit
  goto_program.destructive_insert(loop_exit, copies);

  // update it all
  goto_program.update();
}
