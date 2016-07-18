/*******************************************************************\

Module: Non-concurrency analysis

Author: Daniel Poetzl

\*******************************************************************/

#include "non_concurrent.h"

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool non_concurrentt::is_non_concurrent(
  const placet &place1, const placet &place2)
{
  const ai_cs_stackt &stack1=place1.first;
  locationt loc1=place1.second;
  const ai_cs_stackt &stack2=place2.first;
  locationt loc2=place2.second;

  assert(stack1.is_valid_stack(goto_functions));
  assert(stack2.is_valid_stack(goto_functions));

  ai_cs_stackt::framest::const_iterator it1=stack1.frames.begin();
  ai_cs_stackt::framest::const_iterator it2=stack2.frames.begin();

  while(it1!=stack1.frames.end() && it2!=stack2.frames.end())
  {
    if (*it1!=*it2)
    {
      assert(std::get<0>(*it1)==std::get<0>(*it2));
      break;
    }

    it1++;
    it2++;
  }

  if(it1!=stack1.frames.end())
    loc1=std::get<1>(*it1);

  if(it2!=stack2.frames.end())
    loc2=std::get<1>(*it2);

  assert(loc1->function==loc2->function);

  bool path1=has_path(loc1, loc2);
  bool path2=has_path(loc2, loc1);

  bool non_concurrent=true;

  if(path1)
    non_concurrent&=joined_1(it1, stack1, loc1, loc2);

  if(path2)
    non_concurrent&=joined_1(it2, stack2, loc2, loc1);

  return non_concurrent;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool non_concurrentt::joined_1(
  ai_cs_stackt::framest::const_iterator bound, // exclusive
  const ai_cs_stackt &stack,
  locationt loc1,
  locationt loc2)
{
  bool last_joined=true;
  recursion_sett recursion_set;

  ai_cs_stackt new_stack;

  ai_cs_stackt create_stack;
  locationt create_loc;

  if (bound!=stack.frames.end())
  {
    assert(!stack.frames.empty());

    // forward to reverse
    ai_cs_stackt::framest::const_reverse_iterator b_it(bound);
    b_it--; // dereferencing a reverse iterator gets the *next* element

    ai_cs_stackt::framest::const_reverse_iterator it=stack.frames.crbegin();

    // unwind stack
    while(it!=b_it)
    {
      const ai_cs_stackt::stack_elementt &stack_element=*it;

      irep_idt fun=std::get<0>(stack_element);
      locationt loc=std::get<1>(stack_element);
      assert(loc->function==fun);
      ai_cs_stackt::stack_element_typet kind=std::get<2>(stack_element);

      // reverse to forward
      ai_cs_stackt::framest::const_iterator end_it=it.base();
      new_stack=ai_cs_stackt(); // new empty stack
      assert(new_stack.frames.empty());
      new_stack.frames.insert(
        new_stack.frames.begin(), // need to provide start
        stack.frames.begin(), end_it);

      if (last_joined && kind==ai_cs_stackt::SE_FUNCTION_CALL)
      {
        it++;
        continue;
      }

      const goto_functiont &goto_function=goto_functions.function_map.at(fun);
      assert(goto_function.body_available());
      assert(!goto_function.body.instructions.empty());
      locationt exit=--goto_function.body.instructions.end();
      assert(loc->function==exit->function);

      if(kind==ai_cs_stackt::SE_THREAD_CREATE)
      {
        if (!last_joined)
          return false;

        create_stack=new_stack;
        create_loc=loc;
      }
      else
      {
        assert(kind==ai_cs_stackt::SE_FUNCTION_CALL);
      }

      recursion_set.clear();

      // join on every path to the exit point
      assert(loc->function==exit->function);
      last_joined=joined_2(
          new_stack, loc, exit,
        create_stack, create_loc, // for value lookup
        recursion_set);

      recursion_set.clear();

      if (in_loop.is_in_loop(loc))
      {
        // join on every back path
        last_joined&=joined_2(
            new_stack, loc, loc,
          create_stack, create_loc, // for value lookup
          recursion_set);

        if (!last_joined)
          return false;
      }

      it++;
    }
  }

  // adjust stack
  new_stack=ai_cs_stackt(); // new empty stack
  assert(new_stack.frames.empty());
  new_stack.frames.insert(
    new_stack.frames.begin(), // need to provide start
    stack.frames.begin(), bound);

  // when we reach here and it holds that !last_joined, then a thread
  // was created above that we still need to join

  if(!last_joined)
  {
    recursion_set.clear();

    assert(loc1->function==loc2->function);
    last_joined=joined_2(
      new_stack, loc1, loc2,
      create_stack, create_loc, // for value lookup
      recursion_set);

    recursion_set.clear();

    if(in_loop.is_in_loop(loc1))
    {
      // join on every back path
      assert(loc1->function==loc2->function);
      last_joined&=joined_2(
        new_stack, loc1, loc1,
        create_stack, create_loc, // for value lookup
        recursion_set);
    }

    if(!last_joined)
      return false;
  }

  // now a thread could be created at loc1 that we also need to join

  assert(last_joined);

  if(bound!=stack.frames.end())
  {
    const ai_cs_stackt::stack_elementt &stack_element=*bound;

    locationt loc=std::get<1>(stack_element);
    ai_cs_stackt::stack_element_typet kind=std::get<2>(stack_element);

    assert(loc1==loc);

    if(kind==ai_cs_stackt::SE_THREAD_CREATE)
    {
      create_stack=new_stack;
      create_loc=loc1;

      recursion_set.clear();

      assert(loc1->function==loc2->function);
      last_joined=joined_2(
        new_stack, loc1, loc2,
        create_stack, create_loc, // for value lookup
        recursion_set);

      recursion_set.clear();

      if(in_loop.is_in_loop(loc1))
      {
        // join on every back path
        assert(loc1->function==loc2->function);
        last_joined&=joined_2(
          new_stack, loc1, loc1,
          create_stack, create_loc, // for value lookup
          recursion_set);
      }
    }
  }

  return last_joined;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool non_concurrentt::joined_2(
  const ai_cs_stackt &stack,
  locationt loc1, // path start
  locationt loc2, // path end
  const ai_cs_stackt &create_stack,
  locationt create_loc,
  recursion_sett &recursion_set)
{
  assert(loc1->function==loc2->function);
  irep_idt fun=loc1->function;

  const goto_functiont &goto_function
    =goto_functions.function_map.at(loc1->function);
  assert(goto_function.body_available());
  const goto_programt &goto_program=goto_function.body;

  // look for matching join
  location_sett location_set;
  gather_joins(goto_program, location_set);

  for (locationt join_loc : location_set)
  {
    if (on_all_paths(loc1, join_loc, loc2) &&
        match(stack, join_loc, create_stack, create_loc))
      return true;
  }

  // explore other callees
  location_set.clear();
  gather_function_calls(goto_program, location_set);

  for (locationt call_loc : location_set)
  {
    irep_idt id=misc::get_function_name(call_loc);
    assert(!id.empty());
    if (recursion_set.find(id)!=recursion_set.end())
      continue;

    const goto_functiont &goto_function=goto_functions.function_map.at(id);
    assert(goto_function.body_available());
    const goto_programt &goto_program=goto_function.body;

    locationt entry=goto_program.instructions.begin();
    locationt exit=--goto_program.instructions.end();

    if (on_all_paths(loc1, call_loc, loc2))
    {
      ai_cs_stackt new_stack;
      assert(new_stack.frames.empty());
      new_stack.frames.insert(
        new_stack.frames.begin(),
        stack.frames.begin(), stack.frames.end());

      new_stack.frames.push_back(
        std::make_tuple(fun, call_loc, ai_cs_stackt::SE_FUNCTION_CALL));
      assert(new_stack.is_valid_stack(goto_functions));

      recursion_set.insert(id);

      assert(entry->function==exit->function);
      if(joined_2(
           new_stack, entry, exit,
           create_stack, create_loc,
           recursion_set))
        return true;
    }
  }

  return false;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool non_concurrentt::on_all_paths(
  locationt loc1,
  locationt loc2,
  locationt loc3)
{
  assert(loc1->function==loc2->function);
  assert(loc2->function==loc3->function);

  irep_idt id=loc1->function;
  const goto_functiont &goto_function=goto_functions.function_map.at(id);

  cfg_dominatorst dominators;
  dominators(goto_function.body, loc1);

  cfg_dominatorst::cfgt::entry_mapt::const_iterator it
    =dominators.cfg.entry_map.find(loc3);
  assert(it!=dominators.cfg.entry_map.end());

  int entry_num=it->second;
  const cfg_dominatorst::nodet &node=dominators.cfg[entry_num];

  cfg_dominatorst::target_sett::const_iterator d_it
    =node.dominators.find(loc2);

  return d_it!=node.dominators.end();
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool non_concurrentt::on_all_paths(locationt loc)
{
  irep_idt id=loc->function;
  assert(!id.empty());

  const goto_functiont &goto_function=goto_functions.function_map.at(id);
  assert(goto_function.body_available());
  const goto_programt &goto_program=goto_function.body;
  assert(!goto_program.instructions.empty());

  locationt start=goto_program.instructions.begin();
  locationt end=goto_program.instructions.end();

  return on_all_paths(start, loc, --end);
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool non_concurrentt::on_all_loops(locationt loc1, locationt loc2)
{
  assert(loc1->function==loc2->function);

  irep_idt id=loc1->function;
  const goto_functiont &goto_function=goto_functions.function_map.at(id);

  cfg_dominatorst dominators;
  dominators(goto_function.body, loc1, false);

  cfg_dominatorst::cfgt::entry_mapt::const_iterator it
    =dominators.cfg.entry_map.find(loc1);
  assert(it!=dominators.cfg.entry_map.end());

  int entry_num=it->second;
  const cfg_dominatorst::nodet &node=dominators.cfg[entry_num];

  cfg_dominatorst::target_sett::const_iterator d_it
    =node.dominators.find(loc2);

  return d_it!=node.dominators.end();
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool non_concurrentt::has_path(locationt loc1, locationt loc2)
{
  assert(loc1->function==loc2->function);
  irep_idt id=loc1->function;

  const goto_functiont &goto_function=goto_functions.function_map.at(id);
  assert(goto_function.body_available());
  const goto_programt &goto_program=goto_function.body;

  struct empty_nodet
  {
    empty_nodet() : visited(false) {}
    bool visited;
  };

  typedef procedure_local_cfg_baset<empty_nodet> cfgt;

  cfgt cfg;
  cfg(goto_program);

  unsigned src=cfg.entry_map.at(loc1);
  assert(src < cfg.size());

  cfg.visit_reachable(src);

  unsigned tgt=cfg.entry_map.at(loc2);
  assert(tgt < cfg.size());

  const empty_nodet &node=cfg[tgt];

  return node.visited;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// gather calls to functions we explore
void non_concurrentt::gather_function_calls(
  const goto_programt &goto_program,
  location_sett &location_set)
{
  assert(location_set.empty());

  forall_goto_program_instructions(it, goto_program)
  {
    if(!it->is_function_call())
      continue;

    irep_idt id=misc::get_function_name(it);
    if(id.empty())
      continue;

    std::string sid=id2string(id);

    if(sid==config.ansi_c.create_thread ||
       sid==config.ansi_c.join_thread ||
       sid==config.ansi_c.lock_function ||
       sid==config.ansi_c.unlock_function)
      continue;

    goto_functionst::function_mapt::const_iterator f_it
      =goto_functions.function_map.find(id);

    if(f_it!=goto_functions.function_map.end() && f_it->second.body_available())
      location_set.insert(it);
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void non_concurrentt::gather_joins(
  const goto_programt &goto_program,
  location_sett &location_set)
{
  assert(location_set.empty());

  forall_goto_program_instructions(it, goto_program)
  {
    if(!it->is_function_call())
      continue;

    irep_idt id=misc::get_function_name(it);
    if(id.empty())
      continue;

    std::string sid=id2string(id);
    if (sid==config.ansi_c.join_thread)
      location_set.insert(it);
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool non_concurrentt::all_paths(
  const ai_cs_stackt &stack1,
  locationt loc1,
  const ai_cs_stackt &stack2,
  locationt loc2)
{
  assert(stack1.is_valid_stack(goto_functions));
  assert(stack2.is_valid_stack(goto_functions));

  if (stack1==stack2 && loc1==loc2)
    return true;

  ai_cs_stackt::framest::const_iterator it1=stack1.frames.begin();
  ai_cs_stackt::framest::const_iterator it2=stack2.frames.begin();

  while(it1!=stack1.frames.end() && it2!=stack2.frames.end())
  {
    if (*it1!=*it2)
    {
      assert(std::get<0>(*it1)==std::get<0>(*it2));
      break;
    }

    it1++;
    it2++;
  }

  if(it1!=stack1.frames.end())
    loc1=std::get<1>(*it1);

  if(it2!=stack2.frames.end())
  {
    // final location
    if(!on_all_paths(loc2))
      return false;

    loc2=std::get<1>(*it2);
    it2++;
  }

  assert(loc1->function==loc2->function);

  // after common prefix
  irep_idt id=loc2->function;
  assert(!id.empty());

  const goto_functiont &goto_function=goto_functions.function_map.at(id);
  assert(goto_function.body_available());
  const goto_programt &goto_program=goto_function.body;

  if(!on_all_paths(loc1, loc2, --goto_program.instructions.end()))
    return false;

  // rest of stack
  while(it2!=stack2.frames.end())
  {
    loc2=std::get<1>(*it2);

    if(!on_all_paths(loc2))
      return false;

    it2++;
  }

  return true;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool non_concurrentt::match(
  const ai_cs_stackt &join_stack, locationt join_loc,
  const ai_cs_stackt &create_stack, locationt create_loc) const
{
//#define DEBUG_MATCH
#define EXPR_MATCH

  assert(join_loc->is_function_call());
  assert(create_loc->is_function_call());

  irep_idt join_id=misc::get_function_name(join_loc);
  irep_idt create_id=misc::get_function_name(create_loc);
  assert(id2string(join_id)==config.ansi_c.join_thread);
  assert(id2string(create_id)==config.ansi_c.create_thread);

  const code_function_callt &code_join=to_code_function_call(join_loc->code);
  const code_function_callt &code_create=to_code_function_call(
    create_loc->code);

  typedef code_function_callt::argumentst argumentst;

  const argumentst &join_args=code_join.arguments();
  const argumentst &create_args=code_create.arguments();
  assert(join_args.size()==2);
  assert(create_args.size()==4);

  // thread id parameters
  const exprt &join_expr=join_args[0];
  const exprt &create_expr=create_args[0];

  bool match=false;

#ifdef EXPR_MATCH

  if(create_expr.id()==ID_address_of)
  {
    const address_of_exprt &aoe=to_address_of_expr(create_expr);
    const exprt &o=aoe.object();

    if(join_expr==o)
      return true;
  }

#else

  const dereference_exprt create_deref_expr(
    create_expr, create_expr.type().subtype());

  typedef value_setst::valuest valuest;
  valuest join_dest;
  valuest create_dest;

  value_set_analysis.get_values(
    join_loc, join_stack, join_expr, join_dest, ns);

#ifdef DEBUG_MATCH
  std::cout << "================" << std::endl;
  std::cout << "Join" << std::endl;
  std::cout << join_stack << ", " << join_loc->location_number << std::endl;
  std::cout << join_expr.pretty() << std::endl;

  std::cout << "++++++++++++++++" << std::endl;
  std::cout << "Values" << std::endl;
  std::cout << join_dest.size() << std::endl;
  for(valuest::const_iterator it=join_dest.begin();
      it!=join_dest.end(); it++)
  {
    std::cout << (*it).pretty() << std::endl;
  }
#endif

  // we want the value of the expression *after* the create
  create_loc++;

  value_set_analysis.get_values(
    create_loc, create_stack, create_deref_expr, create_dest, ns);

#ifdef DEBUG_MATCH
  std::cout << "================" << std::endl;
  std::cout << "Create" << std::endl;
  std::cout << create_stack << ", " << create_loc->location_number << std::endl;
  std::cout << create_expr.pretty() << std::endl;
  std::cout << "Created deref expression" << std::endl;
  std::cout << create_deref_expr.pretty() << std::endl;

  std::cout << "++++++++++++++++" << std::endl;
  std::cout << "Values" << std::endl;
  std::cout << create_dest.size() << std::endl;
  for(valuest::const_iterator it=create_dest.begin();
      it!=create_dest.end(); it++)
  {
    std::cout << (*it).pretty() << std::endl;
  }
#endif

  if(join_dest.size()==1 && create_dest.size()==1)
  {
    const exprt &join_obj=join_dest.front();
    const exprt &create_obj=create_dest.front();

    if(join_obj==create_obj)
    {
      if(join_obj.id()!=ID_unknown && join_obj.id()!=ID_invalid)
        match=true;
    }
  }

#ifdef DEBUG_MATCH
  std::cout << "match: " << match << std::endl;
#endif

#endif

  return match;
}
