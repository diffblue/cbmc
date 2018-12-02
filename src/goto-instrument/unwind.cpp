/*******************************************************************\

Module: Loop unwinding

Author: Daniel Kroening, kroening@kroening.com
        Daniel Poetzl

\*******************************************************************/

/// \file
/// Loop unwinding

#include "unwind.h"

#ifdef DEBUG
#include <iostream>
#endif

#include <util/std_expr.h>
#include <util/string_utils.h>
#include <goto-programs/goto_functions.h>

#include "loop_utils.h"

void goto_unwindt::copy_segment(
  const goto_programt::const_targett start,
  const goto_programt::const_targett end, // exclusive
  goto_programt &goto_program) // result
{
  assert(start->location_number<end->location_number);
  assert(goto_program.empty());

  // build map for branch targets inside the loop
  typedef std::map<goto_programt::const_targett, unsigned> target_mapt;
  target_mapt target_map;

  unsigned i=0;

  for(goto_programt::const_targett t=start; t!=end; t++, i++)
    target_map[t]=i;

  // make a copy
  std::vector<goto_programt::targett> target_vector;
  target_vector.reserve(target_map.size());
  assert(target_vector.empty());

  for(goto_programt::const_targett t=start; t!=end; t++)
  {
    goto_programt::targett t_new=goto_program.add_instruction();
    *t_new=*t;
    unwind_log.insert(t_new, t->location_number);
    target_vector.push_back(t_new); // store copied instruction
  }

  assert(goto_program.instructions.size()==target_vector.size());

  // adjust intra-segment gotos
  for(std::size_t i=0; i<target_vector.size(); i++)
  {
    goto_programt::targett t=target_vector[i];

    if(!t->is_goto())
      continue;

    goto_programt::const_targett tgt=t->get_target();

    target_mapt::const_iterator m_it=target_map.find(tgt);

    if(m_it!=target_map.end())
    {
      unsigned j=m_it->second;

      assert(j<target_vector.size());
      t->set_target(target_vector[j]);
    }
  }
}

void goto_unwindt::unwind(
  goto_programt &goto_program,
  const goto_programt::const_targett loop_head,
  const goto_programt::const_targett loop_exit,
  const unsigned k,
  const unwind_strategyt unwind_strategy)
{
  std::vector<goto_programt::targett> iteration_points;
  unwind(goto_program, loop_head, loop_exit, k, unwind_strategy,
         iteration_points);
}

void goto_unwindt::unwind(
  goto_programt &goto_program,
  const goto_programt::const_targett loop_head,
  const goto_programt::const_targett loop_exit,
  const unsigned k,
  const unwind_strategyt unwind_strategy,
  std::vector<goto_programt::targett> &iteration_points)
{
  assert(iteration_points.empty());
  assert(loop_head->location_number<loop_exit->location_number);

  // rest program after unwound part
  goto_programt rest_program;

  if(unwind_strategy==unwind_strategyt::PARTIAL)
  {
    goto_programt::targett t=rest_program.add_instruction();
    unwind_log.insert(t, loop_head->location_number);

    t->make_skip();
    t->source_location=loop_head->source_location;
    t->function=loop_head->function;
    t->location_number=loop_head->location_number;
  }
  else if(unwind_strategy==unwind_strategyt::CONTINUE)
  {
    copy_segment(loop_head, loop_exit, rest_program);
  }
  else
  {
    goto_programt::const_targett t=loop_exit;
    t--;
    assert(t->is_backwards_goto());

    exprt exit_cond = false_exprt(); // default is false

    if(!t->guard.is_true()) // cond in backedge
    {
      exit_cond=t->guard;
      exit_cond.make_not();
    }
    else if(loop_head->is_goto())
    {
      if(loop_head->get_target()==loop_exit) // cond in forward edge
        exit_cond=loop_head->guard;
    }

    goto_programt::targett new_t=rest_program.add_instruction();

    if(unwind_strategy==unwind_strategyt::ASSERT)
      new_t->make_assertion(exit_cond);
    else if(unwind_strategy==unwind_strategyt::ASSUME)
      new_t->make_assumption(exit_cond);
    else
      UNREACHABLE;

    new_t->source_location=loop_head->source_location;
    new_t->function=loop_head->function;
    new_t->location_number=loop_head->location_number;
    unwind_log.insert(new_t, loop_head->location_number);
  }

  assert(!rest_program.empty());

  // to be filled with copies of the loop body
  goto_programt copies;

  if(k!=0)
  {
    iteration_points.resize(k);

    // add a goto before the loop exit to guard against 'fall-out'

    goto_programt::const_targett t_before=loop_exit;
    t_before--;

    if(!t_before->is_goto() || !t_before->guard.is_true())
    {
      goto_programt::targett t_goto=goto_program.insert_before(loop_exit);
      unwind_log.insert(t_goto, loop_exit->location_number);

      t_goto->make_goto(goto_program.const_cast_target(loop_exit));
      t_goto->source_location=loop_exit->source_location;
      t_goto->function=loop_exit->function;
      t_goto->guard=true_exprt();
      t_goto->location_number=loop_exit->location_number;
    }

    // add a skip before the loop exit

    goto_programt::targett t_skip=goto_program.insert_before(loop_exit);
    unwind_log.insert(t_skip, loop_exit->location_number);

    t_skip->make_skip();
    t_skip->source_location=loop_head->source_location;
    t_skip->function=loop_head->function;
    t_skip->location_number=loop_head->location_number;

    // where to go for the next iteration
    goto_programt::targett loop_iter=t_skip;

    // record the exit point of first iteration
    iteration_points[0]=loop_iter;

    // re-direct any branches that go to loop_head to loop_iter

    for(goto_programt::targett
        t=goto_program.const_cast_target(loop_head);
        t!=loop_iter; t++)
    {
      if(!t->is_goto())
        continue;

      if(t->get_target()==loop_head)
        t->set_target(loop_iter);
    }

    // k-1 additional copies
    for(unsigned i=1; i<k; i++)
    {
      goto_programt tmp_program;
      copy_segment(loop_head, loop_exit, tmp_program);
      assert(!tmp_program.instructions.empty());

      iteration_points[i]=--tmp_program.instructions.end();

      copies.destructive_append(tmp_program);
    }
  }
  else
  {
    // insert skip for loop body

    goto_programt::targett t_skip=goto_program.insert_before(loop_head);
    unwind_log.insert(t_skip, loop_head->location_number);

    t_skip->make_skip();
    t_skip->source_location=loop_head->source_location;
    t_skip->function=loop_head->function;
    t_skip->location_number=loop_head->location_number;

    // redirect gotos into loop body
    Forall_goto_program_instructions(i_it, goto_program)
    {
      if(!i_it->is_goto())
        continue;

      goto_programt::const_targett t=i_it->get_target();

      if(t->location_number>=loop_head->location_number &&
         t->location_number<loop_exit->location_number)
      {
        i_it->set_target(t_skip);
      }
    }

    // delete loop body
    goto_program.instructions.erase(loop_head, loop_exit);
  }

  // after unwound part
  copies.destructive_append(rest_program);

  // now insert copies before loop_exit
  goto_program.destructive_insert(loop_exit, copies);
}

void goto_unwindt::unwind(
  goto_programt &goto_program,
  const unwindsett &unwindset,
  const unwind_strategyt unwind_strategy)
{
  for(goto_programt::const_targett i_it=goto_program.instructions.begin();
      i_it!=goto_program.instructions.end();)
  {
#ifdef DEBUG
    symbol_tablet st;
    namespacet ns(st);
    std::cout << "Instruction:\n";
    goto_program.output_instruction(ns, "", std::cout, *i_it);
#endif

    if(!i_it->is_backwards_goto())
    {
      i_it++;
      continue;
    }

    const irep_idt func=i_it->function;
    assert(!func.empty());

    const irep_idt loop_id=
      id2string(func) + "." + std::to_string(i_it->loop_number);

    auto limit=unwindset.get_limit(loop_id, 0);

    if(!limit.has_value())
    {
      // no unwinding given
      i_it++;
      continue;
    }

    goto_programt::const_targett loop_head=i_it->get_target();
    goto_programt::const_targett loop_exit=i_it;
    loop_exit++;
    assert(loop_exit!=goto_program.instructions.end());

    unwind(goto_program, loop_head, loop_exit, *limit, unwind_strategy);

    // necessary as we change the goto program in the previous line
    i_it=loop_exit;
  }
}

void goto_unwindt::operator()(
  goto_functionst &goto_functions,
  const unwindsett &unwindset,
  const unwind_strategyt unwind_strategy)
{
  Forall_goto_functions(it, goto_functions)
  {
    goto_functionst::goto_functiont &goto_function=it->second;

    if(!goto_function.body_available())
      continue;

#ifdef DEBUG
    std::cout << "Function: " << it->first << '\n';
#endif

    goto_programt &goto_program=goto_function.body;

    unwind(goto_program, unwindset, unwind_strategy);
  }
}

// call after calling goto_functions.update()!
jsont goto_unwindt::unwind_logt::output_log_json() const
{
  json_objectt json_result;
  json_arrayt &json_unwound=json_result["unwound"].make_array();

  for(location_mapt::const_iterator it=location_map.begin();
      it!=location_map.end(); it++)
  {
    json_objectt &object=json_unwound.push_back().make_object();

    goto_programt::const_targett target=it->first;
    unsigned location_number=it->second;

    object["originalLocationNumber"]=json_numbert(std::to_string(
      location_number));
    object["newLocationNumber"]=json_numbert(std::to_string(
      target->location_number));
  }

  return std::move(json_result);
}
