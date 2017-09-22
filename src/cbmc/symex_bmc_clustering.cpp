/*******************************************************************\

Module: Clustering Bounded Model Checking for ANSI-C

Author:

\*******************************************************************/

#include <limits>

#include <util/source_location.h>

#include "symex_bmc_clustering.h"
#include <analyses/dirty.h>
#include <goto-programs/wp.h>
#include <util/prefix.h>
#include <iostream>

/*******************************************************************\

Function: symex_bmc_clusteringt::symex_bmc_clusteringt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int symex_bmc_clusteringt::counter=0;

symex_bmc_clusteringt::symex_bmc_clusteringt(
  const namespacet &_ns,
  symbol_tablet &_new_symbol_table,
  symex_targett &_target):
  symex_bmct(_ns, _new_symbol_table, _target)
{
}

void symex_bmc_clusteringt::operator()(
  statet &state,
  const goto_functionst &goto_functions,
  const goto_programt &goto_program)
{
  PRECONDITION(!goto_program.instructions.empty());

  if(state.symex_target==NULL)
  {
    state.source=symex_targett::sourcet(goto_program);
    PRECONDITION(!state.threads.empty());
    PRECONDITION(!state.call_stack().empty());
    state.top().end_of_function=--goto_program.instructions.end();
    state.top().calling_location.pc=state.top().end_of_function;
    state.symex_target=&target;
    state.dirty=new dirtyt(goto_functions);
    symex_transition(state, state.source.pc);
  }

  PRECONDITION(state.top().end_of_function->is_end_function());

  PRECONDITION(!state.id.empty());

  while(!state.call_stack().empty())
  {
    state.locations.push_back(state.source);

    if(learning_symex)
    {
      if(learnt_map.find(state.source)==learnt_map.end())
        learnt_map[state.source]=false_exprt();
    }

#if 0
    std::cout << "[inside operator]: " << state.source.pc->source_location
      << ", " << state.source.pc->type
      << ", " << from_expr(state.guard)
      << "\n";
#endif

    if(state.source.pc->type==GOTO ||
      state.source.pc->type==ASSERT)
    {
      merge_gotos(state); // in case there is pending goto
      const auto &guard=state.source.pc->guard;

      if(state.guard.is_false())
      {
        symex_step(goto_functions, state);
        continue;
      }

      if(state.source.pc->type==GOTO &&
        !guard.is_true() &&
        !guard.is_false())
      {
#if 0
        std::cout << "[GOTO]: " << state.source.pc->source_location
          << ", " << state.source.pc->type
      	  << ", " << from_expr(state.guard)
          << "\n";
#endif
        return;
      }
      else
      {
#if 0
        std::cout << "[ASSERT]: " << state.source.pc->source_location
          << ", " << state.source.pc->type
      	  << ", " << from_expr(state.guard)
          << "\n";
#endif
        return;
      }
    }
    symex_step(goto_functions, state);
  }

  state.dirty=0;
}

void symex_bmc_clusteringt::mock_step(
  statet &state,
  const goto_functionst &goto_functions)
{
  symex_step(goto_functions, state);
}

void symex_bmc_clusteringt::mock_goto_if_condition(
  statet &state,
  const goto_functionst &goto_functions)
{
  if(!state.guard.is_false())
  {
    std::string msg=id2string(state.source.pc->source_location.get_comment());
    if(msg=="")
      msg="__CPROVER_goto_cond: if";
    exprt tmp(state.source.pc->guard);

    clean_expr(tmp, state, false);
    vcc(tmp, msg, state);
  }
}

void symex_bmc_clusteringt::mock_assert_condition(
  statet &state,
  const goto_functionst &goto_functions)
{
  if(!state.guard.is_false())
  {
    std::string msg=id2string(state.source.pc->source_location.get_comment());
    if(msg=="")
      msg="__CPROVER_assert_cond:";
    exprt tmp(state.source.pc->guard);

    clean_expr(tmp, state, false);
    vcc(tmp, msg, state);
  }
}

void symex_bmc_clusteringt::add_goto_if_assumption(
  statet &state,
  const goto_functionst &goto_functions)
{
#if 0
  std::cout << "[add goto if assumption]: "
    << state.source.pc->source_location
    << "; " << from_expr(state.guard) << "\n";
#endif
  PRECONDITION(!state.threads.empty());
  PRECONDITION(!state.call_stack().empty());

  // depth exceeded?
  {
    unsigned max_depth=options.get_unsigned_int_option("depth");
    if(max_depth!=0 && state.depth>max_depth)
      state.guard.add(false_exprt());
    state.depth++;
  }

  if(!state.guard.is_false())
  {
    exprt tmp=state.source.pc->guard;
    clean_expr(tmp, state, false);
    tmp.make_not();
    state.rename(tmp, ns);
    symex_assume(state, tmp);
  }
  merge_gotos(state);
  symex_guard_goto(state, false_exprt());
}

void symex_bmc_clusteringt::mock_goto_else_condition(
  statet &state,
  const goto_functionst &goto_functions)
{
  if(!state.guard.is_false())
  {
    std::string msg=id2string(state.source.pc->source_location.get_comment());
    if(msg=="")
      msg="__CPROVER_goto_cond: else";
    exprt tmp(state.source.pc->guard);
    tmp.make_not();
    clean_expr(tmp, state, false);
    vcc(tmp, msg, state);
  }
}

void symex_bmc_clusteringt::add_goto_else_assumption(
  statet &state,
  const goto_functionst &goto_functions)
{
  #if 0
  std::cout << "\ninstruction type is " << state.source.pc->type << '\n';
  std::cout << "Location: " << state.source.pc->source_location << '\n';
  std::cout << "Guard: " << from_expr(ns, "", state.guard.as_expr()) << '\n';
  std::cout << "Code: " << from_expr(ns, "", state.source.pc->code) << '\n';
  #endif

  PRECONDITION(!state.threads.empty());
  PRECONDITION(!state.call_stack().empty());

  // depth exceeded?
  {
    unsigned max_depth=options.get_unsigned_int_option("depth");
    if(max_depth!=0 && state.depth>max_depth)
      state.guard.add(false_exprt());
    state.depth++;
  }

  if(!state.guard.is_false())
  {
    exprt tmp=state.source.pc->guard;
    clean_expr(tmp, state, false);
    state.rename(tmp, ns);
    symex_assume(state, tmp);
  }

  symex_guard_goto(state, true_exprt());
}

void symex_bmc_clusteringt::record(statet &state)
{
  std::string id="state"+std::to_string(counter);
  state.id=id;
  ++counter;
}

void symex_bmc_clusteringt::create_a_cluster(
  statet &state,
  symex_targett &equation)
{
  record(state);
  clusters[state.id]=state;
  clusters[state.id].symex_target=&equation;
}

goto_symext::statet& symex_bmc_clusteringt::cluster(const std::string &id)
{
  PRECONDITION(clusters.find(id)!=clusters.end());
  return clusters[id];
}

goto_symext::statet& symex_bmc_clusteringt::cluster(const statet &state)
{
  return cluster(state.id);
}

void symex_bmc_clusteringt::symex_guard_goto(statet &state, const exprt &guard)
{
  const goto_programt::instructiont &instruction=*state.source.pc;
  statet::framet &frame=state.top();

  exprt old_guard=guard;
  clean_expr(old_guard, state, false);

  exprt new_guard=old_guard;
  state.rename(new_guard, ns);
  do_simplify(new_guard);

  if(new_guard.is_false() ||
     state.guard.is_false())
  {
    if(!state.guard.is_false())
    {
      state.symex_target->location(state.guard.as_expr(), state.source);
    }
    symex_transition(state);

    return; // nothing to do
  }

  state.symex_target->goto_instruction(
    state.guard.as_expr(),
    new_guard,
    state.source);

  PRECONDITION(!instruction.targets.empty());

  // we only do deterministic gotos for now
  if(instruction.targets.size()!=1)
    throw "no support for non-deterministic gotos";

  goto_programt::const_targett goto_target=
    instruction.get_target();

  bool forward=!instruction.is_backwards_goto();
  if(!forward) // backwards?
  {
    // is it label: goto label; or while(cond); - popular in SV-COMP
    if(goto_target==state.source.pc ||
       (instruction.incoming_edges.size()==1 &&
        *instruction.incoming_edges.begin()==goto_target))
    {
      // generate assume(false) or a suitable negation if this
      // instruction is a conditional goto
      exprt negated_cond;

      if(new_guard.is_true())
        negated_cond=false_exprt();
      else
        negated_cond=not_exprt(new_guard);

      symex_assume(state, negated_cond);

      // next instruction
      symex_transition(state);
      return;
    }

    unsigned &unwind=
      frame.loop_iterations[goto_programt::loop_id(state.source.pc)].count;
    unwind++;

    // continue unwinding?
    if(get_unwind(state.source, unwind))
    {
      loop_bound_exceeded(state, new_guard);

      // next instruction
      symex_transition(state);
      return;
    }

    if(new_guard.is_true())
    {
      symex_transition(state, goto_target, true);
      return; // nothing else to do
    }
  }

  goto_programt::const_targett new_state_pc, state_pc;
  symex_targett::sourcet original_source=state.source;

  if(forward)
  {
    new_state_pc=goto_target;
    state_pc=state.source.pc;
    state_pc++;

    // skip dead instructions
    if(new_guard.is_true())
    {
      while(state_pc!=goto_target && !state_pc->is_target())
      {
        ++state_pc;
      }
    }

    if(state_pc==goto_target)
    {
      symex_transition(state, goto_target);
      return; // nothing else to do
    }
  }
  else
  {
    new_state_pc=state.source.pc;
    new_state_pc++;
    state_pc=goto_target;
  }

  // put into state-queue
  statet::goto_state_listt &goto_state_list=
    state.top().goto_state_map[new_state_pc];

  goto_state_list.push_back(statet::goto_statet(state));
  statet::goto_statet &new_state=goto_state_list.back();

  symex_transition(state, state_pc, !forward);

  // adjust guards
  if(new_guard.is_true())
  {
    state.guard.make_false();
  }
  else
  {
    // produce new guard symbol
    exprt guard_expr;

    if(new_guard.id()==ID_symbol ||
       (new_guard.id()==ID_not &&
        new_guard.operands().size()==1 &&
        new_guard.op0().id()==ID_symbol))
      guard_expr=new_guard;
    else
    {
      symbol_exprt guard_symbol_expr=
        symbol_exprt(guard_identifier, bool_typet());
      exprt new_rhs=new_guard;
      new_rhs.make_not();

      ssa_exprt new_lhs(guard_symbol_expr);
      state.rename(new_lhs, ns, goto_symex_statet::L1);
      state.assignment(new_lhs, new_rhs, ns, true, false);

      guardt guard;

      state.symex_target->assignment(
        guard.as_expr(),
        new_lhs, new_lhs, guard_symbol_expr,
        new_rhs,
        original_source,
        symex_targett::assignment_typet::GUARD);

      guard_expr=guard_symbol_expr;
      guard_expr.make_not();
      state.rename(guard_expr, ns);
    }

    if(forward)
    {
      new_state.guard.add(guard_expr);
      guard_expr.make_not();
      state.guard.add(guard_expr);
    }
    else
    {
      state.guard.add(guard_expr);
      guard_expr.make_not();
      new_state.guard.add(guard_expr);
    }
  }
}

void symex_bmc_clusteringt::backtrack_learn(statet &state)
{
  exprt learnt_expr=true_exprt();
  for(auto it=state.locations.rbegin(); it!=state.locations.rend(); ++it)
  {
    if(it->pc->type==ASSERT)
    {
      std::cout << "backtrack learn: " <<it->pc->source_location
        << ", assert: " << from_expr(it->pc->guard) << "\n";
      learnt_expr=and_exprt(learnt_expr, it->pc->guard);
      std::cout << "***learnt: " << from_expr(learnt_expr) << "\n";
    }
    else if(it->pc->type==ASSUME)
      learnt_expr=or_exprt(learnt_expr, it->pc->guard);
    else if(it->pc->type==GOTO)
    {
      exprt expr=it->pc->guard;
      std::cout << "backtrack learn: " <<it->pc->source_location
        << ", goto: " << from_expr(expr) << "\n";
      if(it->goto_branch==symex_targett::sourcet::goto_brancht::IF)
        expr.make_not();
      learnt_expr=and_exprt(learnt_expr, expr);
      std::cout << "***learnt: " << from_expr(learnt_expr) << "\n";
      std::cout << "[learnt]: " << from_expr(learnt_map[*it]) << "\n";
#if 0
      // manual weakest-pre for goto
      codet code=it->pc->code;
      code.set_statement(ID_assume);
      code.operands().push_back(it->pc->guard);
      std::cout << "it->goto_branch: " << it->goto_branch
        << ", " << from_expr(code.op0()) << "\n";
      if(it->goto_branch==symex_targett::sourcet::goto_brancht::IF)
        code.op0().make_not();
      learnt_expr=wp(code, learnt_expr, ns);
      exprt tmp(it->pc->guard);
      if(it->goto_branch==symex_targett::sourcet::goto_brancht::IF)
        tmp.make_not();

      POSTCONDITION(learnt_expr.operands().size()==2);

      or_exprt or_expr;
      or_expr.operands().push_back(learnt_expr.op0());
      or_expr.operands().push_back(learnt_expr.op1());
      or_expr.op0().make_not();
      // manually (!A||B)&&C to !A&&C || B&&C
      or_expr.op0()=and_exprt(or_expr.op0(), tmp);
      or_expr.op1()=and_exprt(or_expr.op1(), tmp);
      learnt_expr=or_expr;
#endif
    }
    else if(it->pc->type==ASSIGN)
    {
      learnt_expr=wp(it->pc->code, learnt_expr, ns);
    }

    if(it->pc->type==GOTO) // it->pc->incoming_edges.size()>1)
    {
      if(it->pc->guard.is_true() || it->pc->guard.is_false())
        continue;
#if 0
      bool backwards_loop=false;
      for(auto &in : it->pc->incoming_edges)
      {
        if(it->pc->location_number<in->location_number)
        {
          backwards_loop=true;
          break;
        }
      }
      if(backwards_loop)
        continue;
#endif
      learnt_map[*it]=or_exprt(learnt_map[*it], learnt_expr);
      do_simplify(learnt_map[*it]);
      std::cout << "[learnt-B]: " << from_expr(learnt_map[*it]) << "\n\n";
    }
  }
  for(auto &x : learnt_map) do_simplify(x.second);
}

void symex_bmc_clusteringt::print_learnt_map()
{
  std::cout << "\n[***The map learnt ***]\n";
  for(auto &x : learnt_map)
  {
    if(x.second.is_false())
      continue;
    std::cout << x.first.pc->source_location;
    std::cout << ": ";
    std::cout << from_expr(x.second) << "\n";
  }
}

void symex_bmc_clusteringt::add_latest_learnt_info(
  statet &state,
  const goto_functionst &goto_functions)
{
  auto &x=state.locations.back();
  if(learnt_map[x].is_false())
    return;
  std::cout << "Added learnt info: " << x.pc->source_location << ","
    << from_expr(learnt_map[x]) << ", "
    << state.source.pc->source_location << "\n";
  exprt tmp(learnt_map[x]);
  tmp.make_not();
  clean_expr(tmp, state, false);
  symex_assume(state, tmp);
}
