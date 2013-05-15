/*******************************************************************\

Module: loop unwinding

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

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
  std::vector<goto_programt::targett> &exit_points)
{
  assert(k!=0);
  
  exit_points.resize(k);
  
  // add a skip after loop as the new loop-end
  {
    locationt location=loop_exit->location;
    irep_idt function=loop_exit->function;
    goto_program.insert_before_swap(loop_exit);
    loop_exit->make_skip();
    loop_exit->location=location;
    loop_exit->function=function;
  }

  // record exit point of original
  exit_points[0]=loop_exit;

  goto_programt::targett loop_exit_next=loop_exit;
  loop_exit_next++;

  // build a map for branch targets inside the loop
  std::map<goto_programt::targett, unsigned> target_map;

  { 
    unsigned count=0;
    for(goto_programt::targett t=loop_head;
        t!=loop_exit_next; t++, count++)
    {
      assert(t!=goto_program.instructions.end());
      target_map[t]=count;
    }
  }

  // re-direct any branches to loop_head to loop_exit
  
  for(goto_programt::targett t=loop_head;
      t!=loop_exit; t++)
  {
    assert(t!=goto_program.instructions.end());
    for(goto_programt::instructiont::targetst::iterator
        t_it=t->targets.begin();
        t_it!=t->targets.end();
        t_it++)
      if(*t_it==loop_head) *t_it=loop_exit;
  }
  
  // we make k-1 copies, to be inserted after loop_exit
  goto_programt copies;

  for(unsigned i=1; i<k; i++)
  {
    // make a copy
    std::vector<goto_programt::targett> target_vector;
    target_vector.reserve(target_map.size());

    for(goto_programt::targett t=loop_head;
        t!=loop_exit_next; t++)
    {
      assert(t!=goto_program.instructions.end());
      goto_programt::targett copied_t=copies.add_instruction();
      *copied_t=*t;
      target_vector.push_back(copied_t);
    }

    // record exit point of this copy
    exit_points[i]=target_vector.back();
    
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
  
  // now insert copies
  goto_program.destructive_insert(++loop_exit, copies);

  // update it all
  goto_program.update();
}
