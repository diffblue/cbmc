/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#include "accelerate.h"

#include <analyses/natural_loops.h>

#include <goto-programs/goto_functions.h>

#include <util/arith_tools.h>
#include <util/find_symbols.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include <iostream>
#include <list>

#include "accelerator.h"
#include "enumerating_loop_acceleration.h"
#include "overflow_instrumenter.h"
#include "path.h"
#include "scratch_program.h"
#include "util.h"

#ifdef DEBUG
#  include <util/format_expr.h>
#endif

goto_programt::targett acceleratet::find_back_jump(
  goto_programt::targett loop_header)
{
  natural_loops_mutablet::natural_loopt &loop =
    natural_loops.loop_map.at(loop_header);
  goto_programt::targett back_jump=loop_header;

  for(const auto &t : loop)
  {
    if(
      t->is_goto() && t->condition().is_true() && t->targets.size() == 1 &&
      t->targets.front() == loop_header &&
      t->location_number > back_jump->location_number)
    {
      back_jump=t;
    }
  }

  return back_jump;
}

bool acceleratet::contains_nested_loops(goto_programt::targett &loop_header)
{
  natural_loops_mutablet::natural_loopt &loop =
    natural_loops.loop_map.at(loop_header);

  for(const auto &t : loop)
  {
    if(t->is_backwards_goto())
    {
      if(t->targets.size()!=1 ||
         t->get_target()!=loop_header)
      {
        return true;
      }
    }

    // Header of some other loop?
    if(t != loop_header && natural_loops.is_loop_header(t))
    {
      return true;
    }
  }

  return false;
}

int acceleratet::accelerate_loop(goto_programt::targett &loop_header)
{
  pathst loop_paths, exit_paths;
  goto_programt::targett back_jump=find_back_jump(loop_header);
  int num_accelerated=0;
  std::list<path_acceleratort> accelerators;
  natural_loops_mutablet::natural_loopt &loop =
    natural_loops.loop_map.at(loop_header);

  if(contains_nested_loops(loop_header))
  {
    // For now, only accelerate innermost loops.
#ifdef DEBUG
    std::cout << "Not accelerating an outer loop\n";
#endif
    return 0;
  }

  goto_programt::targett overflow_loc;
  make_overflow_loc(loop_header, back_jump, overflow_loc);
  program.update();

#if 1
  enumerating_loop_accelerationt acceleration(
    message_handler,
    symbol_table,
    goto_functions,
    program,
    loop,
    loop_header,
    accelerate_limit,
    guard_manager);
#else
  disjunctive_polynomial_accelerationt
    acceleration(symbol_table, goto_functions, program, loop, loop_header);
#endif

  path_acceleratort accelerator;

  while(acceleration.accelerate(accelerator) &&
        (accelerate_limit < 0 ||
         num_accelerated < accelerate_limit))
  {
    // set_dirty_vars(accelerator);

    if(is_underapproximate(accelerator))
    {
      // We have some underapproximated variables -- just punt for now.
#ifdef DEBUG
      std::cout << "Not inserting accelerator because of underapproximation\n";
#endif

      continue;
    }

    accelerators.push_back(accelerator);
    num_accelerated++;

#ifdef DEBUG
    std::cout << "Accelerated path:\n";
    output_path(accelerator.path, program, ns, std::cout);

    std::cout << "Accelerator has "
              << accelerator.pure_accelerator.instructions.size()
              << " instructions\n";
#endif
  }

  goto_programt::instructiont skip(SKIP);
  program.insert_before_swap(loop_header, skip);

  goto_programt::targett new_inst=loop_header;
  ++new_inst;

  loop.insert_instruction(new_inst);

  std::cout << "Overflow loc is " << overflow_loc->location_number << '\n';
  std::cout << "Back jump is " << back_jump->location_number << '\n';

  for(std::list<path_acceleratort>::iterator it=accelerators.begin();
      it!=accelerators.end();
      ++it)
  {
    subsumed_patht inserted(it->path);

    insert_accelerator(loop_header, back_jump, *it, inserted);
    subsumed.push_back(inserted);
    num_accelerated++;
  }

  return num_accelerated;
}

void acceleratet::insert_accelerator(
  goto_programt::targett &loop_header,
  goto_programt::targett &back_jump,
  path_acceleratort &accelerator,
  subsumed_patht &subsumed_path)
{
  insert_looping_path(
    loop_header,
    back_jump,
    accelerator.pure_accelerator,
    subsumed_path.accelerator);

  if(!accelerator.overflow_path.instructions.empty())
  {
    insert_looping_path(
      loop_header, back_jump, accelerator.overflow_path, subsumed_path.residue);
  }
}

/*
 * Insert a looping path (usually an accelerator) into a goto-program,
 * beginning at loop_header and jumping back to loop_header via back_jump.
 * Stores the locations at which the looping path was added in inserted_path.
 *
 * THIS DESTROYS looping_path!!
 */
void acceleratet::insert_looping_path(
  goto_programt::targett &loop_header,
  goto_programt::targett &back_jump,
  goto_programt &looping_path,
  patht &inserted_path)
{
  goto_programt::targett loop_body=loop_header;
  ++loop_body;

  goto_programt::targett jump = program.insert_before(
    loop_body,
    goto_programt::make_goto(
      loop_body,
      side_effect_expr_nondett(bool_typet(), loop_body->source_location()),
      loop_body->source_location()));

  program.destructive_insert(loop_body, looping_path);

  jump = program.insert_before(
    loop_body, goto_programt::make_goto(back_jump, true_exprt()));

  for(goto_programt::targett t=loop_header;
      t!=loop_body;
      ++t)
  {
    inserted_path.push_back(path_nodet(t));
  }

  inserted_path.push_back(path_nodet(back_jump));
}

void acceleratet::make_overflow_loc(
  goto_programt::targett loop_header,
  goto_programt::targett &loop_end,
  goto_programt::targett &overflow_loc)
{
  symbolt overflow_sym=utils.fresh_symbol("accelerate::overflow", bool_typet());
  const exprt &overflow_var=overflow_sym.symbol_expr();
  natural_loops_mutablet::natural_loopt &loop =
    natural_loops.loop_map.at(loop_header);
  overflow_instrumentert instrumenter(program, overflow_var, symbol_table);

  for(const auto &loop_instruction : loop)
  {
    overflow_locs[loop_instruction] = goto_programt::targetst();
    goto_programt::targetst &added = overflow_locs[loop_instruction];

    instrumenter.add_overflow_checks(loop_instruction, added);
    for(const auto &new_instruction : added)
      loop.insert_instruction(new_instruction);
  }

  goto_programt::targett t = program.insert_after(
    loop_header,
    goto_programt::make_assignment(code_assignt(overflow_var, false_exprt())));
  t->swap(*loop_header);
  loop.insert_instruction(t);
  overflow_locs[loop_header].push_back(t);

  overflow_loc = program.insert_after(loop_end, goto_programt::make_skip());
  overflow_loc->swap(*loop_end);
  loop.insert_instruction(overflow_loc);

  goto_programt::targett t2 = program.insert_after(
    loop_end, goto_programt::make_goto(overflow_loc, not_exprt(overflow_var)));
  t2->swap(*loop_end);
  overflow_locs[overflow_loc].push_back(t2);
  loop.insert_instruction(t2);

  goto_programt::targett tmp=overflow_loc;
  overflow_loc=loop_end;
  loop_end=tmp;
}

void acceleratet::restrict_traces()
{
  trace_automatont automaton(program);

  for(subsumed_pathst::iterator it=subsumed.begin();
       it!=subsumed.end();
       ++it)
  {
    if(!it->subsumed.empty())
    {
#ifdef DEBUG
      namespacet ns(symbol_table);
      std::cout << "Restricting path:\n";
      output_path(it->subsumed, program, ns, std::cout);
#endif

      automaton.add_path(it->subsumed);
    }

    patht double_accelerator;
    patht::iterator jt=double_accelerator.begin();
    double_accelerator.insert(
      jt, it->accelerator.begin(), it->accelerator.end());
    double_accelerator.insert(
      jt, it->accelerator.begin(), it->accelerator.end());

#ifdef DEBUG
      namespacet ns(symbol_table);
      std::cout << "Restricting path:\n";
      output_path(double_accelerator, program, ns, std::cout);
#endif
    automaton.add_path(double_accelerator);
  }

  std::cout << "Building trace automaton...\n";

  automaton.build();
  insert_automaton(automaton);
}

void acceleratet::set_dirty_vars(path_acceleratort &accelerator)
{
  for(std::set<exprt>::iterator it=accelerator.dirty_vars.begin();
      it!=accelerator.dirty_vars.end();
      ++it)
  {
    expr_mapt::iterator jt=dirty_vars_map.find(*it);
    exprt dirty_var;

    if(jt==dirty_vars_map.end())
    {
      scratch_programt scratch(symbol_table, message_handler, guard_manager);
      symbolt new_sym=utils.fresh_symbol("accelerate::dirty", bool_typet());
      dirty_var=new_sym.symbol_expr();
      dirty_vars_map[*it]=dirty_var;
    }
    else
    {
      dirty_var=jt->second;
    }

#ifdef DEBUG
    std::cout << "Setting dirty flag " << format(dirty_var) << " for "
              << format(*it) << '\n';
#endif

    accelerator.pure_accelerator.add(
      goto_programt::make_assignment(code_assignt(dirty_var, true_exprt())));
  }
}

void acceleratet::add_dirty_checks()
{
  for(expr_mapt::iterator it=dirty_vars_map.begin();
      it!=dirty_vars_map.end();
      ++it)
  {
    goto_programt::instructiont assign =
      goto_programt::make_assignment(code_assignt(it->second, false_exprt()));
    program.insert_before_swap(program.instructions.begin(), assign);
  }

  goto_programt::targett next;

  for(goto_programt::targett it=program.instructions.begin();
       it!=program.instructions.end();
       it=next)
  {
    next=it;
    ++next;

    // If this is an assign to a tracked variable, clear the dirty flag.
    // Note: this order of insertions means that we assume each of the read
    // variables is clean _before_ clearing any dirty flags.
    if(it->is_assign())
    {
      const exprt &lhs = it->assign_lhs();
      expr_mapt::iterator dirty_var=dirty_vars_map.find(lhs);

      if(dirty_var!=dirty_vars_map.end())
      {
        goto_programt::instructiont clear_flag = goto_programt::make_assignment(
          code_assignt(dirty_var->second, false_exprt()));
        program.insert_before_swap(it, clear_flag);
      }
    }

    // Find which symbols are read, i.e. those appearing in a guard or on
    // the right hand side of an assignment.  Assume each is not dirty.
    find_symbols_sett read;

    if(it->has_condition())
      find_symbols_or_nexts(it->condition(), read);

    if(it->is_assign())
    {
      find_symbols_or_nexts(it->assign_rhs(), read);
    }

    for(find_symbols_sett::iterator jt=read.begin();
        jt!=read.end();
        ++jt)
    {
      const exprt &var=ns.lookup(*jt).symbol_expr();
      expr_mapt::iterator dirty_var=dirty_vars_map.find(var);

      if(dirty_var==dirty_vars_map.end())
      {
        continue;
      }

      goto_programt::instructiont not_dirty =
        goto_programt::make_assumption(not_exprt(dirty_var->second));
      program.insert_before_swap(it, not_dirty);
    }
  }
}

bool acceleratet::is_underapproximate(path_acceleratort &accelerator)
{
  for(std::set<exprt>::iterator it=accelerator.dirty_vars.begin();
      it!=accelerator.dirty_vars.end();
      ++it)
  {
    if(it->id()==ID_symbol && it->type() == bool_typet())
    {
      const irep_idt &id=to_symbol_expr(*it).get_identifier();
      const symbolt &sym = symbol_table.lookup_ref(id);

      if(sym.module=="scratch")
      {
        continue;
      }
    }

#ifdef DEBUG
    std::cout << "Underapproximate variable: " << format(*it) << '\n';
#endif
    return true;
  }

  return false;
}

symbolt acceleratet::make_symbol(std::string name, typet type)
{
  symbolt ret;
  ret.module="accelerate";
  ret.name=name;
  ret.base_name=name;
  ret.pretty_name=name;
  ret.type=type;

  symbol_table.add(ret);

  return ret;
}

void acceleratet::decl(symbol_exprt &, goto_programt::targett)
{
#if 0
  goto_programt::targett decl=program.insert_before(t);
  code_declt code(sym);

  decl->make_decl();
  decl->code=code;
#endif
}

void acceleratet::decl(symbol_exprt &sym, goto_programt::targett t, exprt init)
{
  decl(sym, t);

  program.insert_before(
    t, goto_programt::make_assignment(code_assignt(sym, init)));
}

void acceleratet::insert_automaton(trace_automatont &automaton)
{
  symbolt state_sym=make_symbol("trace_automaton::state",
      unsigned_poly_type());
  symbolt next_state_sym=make_symbol("trace_automaton::next_state",
      unsigned_poly_type());
  symbol_exprt state=state_sym.symbol_expr();
  symbol_exprt next_state=next_state_sym.symbol_expr();

  trace_automatont::sym_mapt transitions;
  state_sett accept_states;

  automaton.get_transitions(transitions);
  automaton.accept_states(accept_states);

  std::cout
    << "Inserting trace automaton with "
    << automaton.num_states() << " states, "
    << accept_states.size() << " accepting states and "
    << transitions.size() << " transitions\n";

  // Declare the variables we'll use to encode the state machine.
  goto_programt::targett t=program.instructions.begin();
  decl(state, t, from_integer(automaton.init_state(), state.type()));
  decl(next_state, t);

  // Now for each program location that appears as a symbol in the
  // trace automaton, add the appropriate code to drive the state
  // machine.
  for(const auto &sym : automaton.alphabet)
  {
    scratch_programt state_machine{
      symbol_table, message_handler, guard_manager};
    trace_automatont::sym_range_pairt p=transitions.equal_range(sym);

    build_state_machine(p.first, p.second, accept_states, state, next_state,
        state_machine);

    program.insert_before_swap(sym, state_machine);
  }
}

void acceleratet::build_state_machine(
  trace_automatont::sym_mapt::iterator begin,
  trace_automatont::sym_mapt::iterator end,
  state_sett &accept_states,
  symbol_exprt state,
  symbol_exprt next_state,
  scratch_programt &state_machine)
{
  std::map<unsigned int, unsigned int> successor_counts;
  unsigned int max_count=0;
  unsigned int likely_next=0;

  // Optimisation: find the most common successor state and initialise
  // next_state to that value.  This reduces the size of the state machine
  // driver substantially.
  for(trace_automatont::sym_mapt::iterator p=begin; p!=end; ++p)
  {
    trace_automatont::state_pairt state_pair=p->second;
    unsigned int to=state_pair.second;
    unsigned int count=0;

    if(successor_counts.find(to)==successor_counts.end())
    {
      count=1;
    }
    else
    {
      count=successor_counts[to] + 1;
    }

    successor_counts[to]=count;

    if(count > max_count)
    {
      max_count=count;
      likely_next=to;
    }
  }

  // Optimisation: if there is only one possible successor state, just
  // jump straight to it instead of driving the whole machine.
  if(successor_counts.size()==1)
  {
    if(accept_states.find(likely_next)!=accept_states.end())
    {
      // It's an accept state.  Just assume(false).
      state_machine.assume(false_exprt());
    }
    else
    {
      state_machine.assign(state,
          from_integer(likely_next, next_state.type()));
    }

    return;
  }

  state_machine.assign(next_state,
      from_integer(likely_next, next_state.type()));

  for(trace_automatont::sym_mapt::iterator p=begin; p!=end; ++p)
  {
    trace_automatont::state_pairt state_pair=p->second;
    unsigned int from=state_pair.first;
    unsigned int to=state_pair.second;

    if(to==likely_next)
    {
      continue;
    }

    // We're encoding the transition
    //
    //   from -loc-> to
    //
    // which we encode by inserting:
    //
    //   next_state=(state==from) ? to : next_state;
    //
    // just before loc.
    equal_exprt guard(state, from_integer(from, state.type()));
    if_exprt rhs(guard, from_integer(to, next_state.type()), next_state);
    state_machine.assign(next_state, rhs);
  }

  // Update the state and assume(false) if we've hit an accept state.
  state_machine.assign(state, next_state);

  for(state_sett::iterator it=accept_states.begin();
      it!=accept_states.end();
      ++it)
  {
    state_machine.assume(
      not_exprt(equal_exprt(state, from_integer(*it, state.type()))));
  }
}

int acceleratet::accelerate_loops()
{
  int num_accelerated=0;

  for(natural_loops_mutablet::loop_mapt::iterator it =
      natural_loops.loop_map.begin();
      it!=natural_loops.loop_map.end();
      ++it)
  {
    goto_programt::targett t=it->first;
    num_accelerated += accelerate_loop(t);
  }

  program.update();

  if(num_accelerated > 0)
  {
    std::cout << "Engaging crush mode...\n";

    restrict_traces();
    // add_dirty_checks();
    program.update();

    std::cout << "Crush mode engaged.\n";
  }

  return num_accelerated;
}

void accelerate_functions(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  bool use_z3,
  guard_managert &guard_manager)
{
  for(auto &gf_entry : goto_model.goto_functions.function_map)
  {
    std::cout << "Accelerating function " << gf_entry.first << '\n';
    acceleratet accelerate(
      gf_entry.second.body, goto_model, message_handler, use_z3, guard_manager);

    int num_accelerated=accelerate.accelerate_loops();

    if(num_accelerated > 0)
    {
      std::cout << "Added " << num_accelerated
                << " accelerator(s)\n";
    }
  }
}
