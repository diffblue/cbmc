#include <analyses/natural_loops.h>

#include <goto-programs/goto_functions.h>

#include <util/std_expr.h>
#include <util/arith_tools.h>

#include <iostream>
#include <list>

#include "accelerate.h"
#include "path.h"
#include "polynomial_accelerator.h"
#include "enumerating_loop_acceleration.h"
#include "disjunctive_polynomial_acceleration.h"
#include "overflow_instrumenter.h"
//#include "symbolic_accelerator.h"

#define DEBUG

using namespace std;

goto_programt::targett acceleratet::find_back_jump(
    goto_programt::targett loop_header) {
  natural_loops_mutablet::natural_loopt &loop =
    natural_loops.loop_map[loop_header];
  goto_programt::targett back_jump = loop_header;

  for (natural_loops_mutablet::natural_loopt::iterator it = loop.begin();
       it != loop.end();
       ++it) {
    goto_programt::targett t = *it;
    if (t->is_goto() &&
        t->guard.is_true() &&
        t->targets.size() == 1 &&
        t->targets.front() == loop_header &&
        t->location_number > back_jump->location_number) {
      back_jump = t;
    }
  }

  return back_jump;
}

int acceleratet::accelerate_loop(goto_programt::targett &loop_header) {
  pathst loop_paths, exit_paths;
  goto_programt::targett back_jump = find_back_jump(loop_header);
  int num_accelerated = 0;
  list<path_acceleratort> accelerators;
  natural_loops_mutablet::natural_loopt &loop =
    natural_loops.loop_map[loop_header];

  goto_programt::targett overflow_loc;
  make_overflow_loc(loop_header, back_jump, overflow_loc);
  program.update();

  /*
  enumerating_loop_accelerationt acceleration(symbol_table, goto_functions,
      program, loop, loop_header, accelerate_limit);
      */
  disjunctive_polynomial_accelerationt acceleration(symbol_table, goto_functions,
      program, loop, loop_header);

  path_acceleratort accelerator;

  while (acceleration.accelerate(accelerator)) {
    accelerators.push_back(accelerator);
    num_accelerated++;

#ifdef DEBUG
    std::cout << "Accelerated path:" << std::endl;
    output_path(accelerator.path, program, ns, std::cout);
#endif
  }

  goto_programt::instructiont skip(SKIP);
  program.insert_before_swap(loop_header, skip);

  goto_programt::targett new_inst = loop_header;
  ++new_inst;

  loop.insert(new_inst);


  std::cout << "Overflow loc is " << overflow_loc->location_number << std::endl;
  std::cout << "Back jump is " << back_jump->location_number << std::endl;

  for (list<path_acceleratort>::iterator it = accelerators.begin();
       it != accelerators.end();
       ++it) {
    subsumed_patht inserted(it->path);

    //inserted.subsumed.push_back(path_nodet(back_jump));
    //inserted.subsumed.back().loc = back_jump;

    insert_accelerator(loop_header, back_jump, *it, inserted);
    subsumed.push_back(inserted);
    num_accelerated++;
  }

  return num_accelerated;
}

void acceleratet::insert_accelerator(goto_programt::targett &loop_header,
    goto_programt::targett &back_jump,
    path_acceleratort &accelerator,
    subsumed_patht &subsumed) {
  insert_looping_path(loop_header, back_jump, accelerator.pure_accelerator,
      subsumed.accelerator);

  if (!accelerator.overflow_path.instructions.empty()) {
    insert_looping_path(loop_header, back_jump, accelerator.overflow_path,
        subsumed.residue);
  }
}

/*
 * Insert a looping path (usually an accelerator) into a goto-program,
 * beginning at loop_header and jumping back to loop_header via back_jump.
 * Stores the locations at which the looping path was added in inserted_path.
 *
 * THIS DESTROYS looping_path!!
 */
void acceleratet::insert_looping_path(goto_programt::targett &loop_header,
    goto_programt::targett &back_jump,
    goto_programt &looping_path,
    patht &inserted_path) {
  goto_programt::targett loop_body = loop_header;
  ++loop_body;

  goto_programt::targett jump = program.insert_before(loop_body);
  jump->make_goto();
  jump->guard = side_effect_expr_nondett(bool_typet());
  jump->targets.push_back(loop_body);

  program.destructive_insert(loop_body, looping_path);

  jump = program.insert_before(loop_body);
  jump->make_goto();
  jump->guard = true_exprt();
  jump->targets.push_back(back_jump);

  for (goto_programt::targett t = loop_header;
       t != loop_body;
       ++t) {
    inserted_path.push_back(path_nodet(t));
  }

  inserted_path.push_back(path_nodet(back_jump));
}

void acceleratet::make_overflow_loc(goto_programt::targett loop_header,
                                    goto_programt::targett &loop_end,
                                    goto_programt::targett &overflow_loc) {
  scratch_programt scratch(symbol_table);
  symbolt overflow_sym = scratch.fresh_symbol("accelerate::overflow", bool_typet());
  symbol_table.add(overflow_sym);

  const exprt &overflow_var = overflow_sym.symbol_expr();
  natural_loops_mutablet::natural_loopt &loop =
    natural_loops.loop_map[loop_header];
  overflow_instrumentert instrumenter(program, overflow_var, symbol_table);

  for (natural_loops_mutablet::natural_loopt::iterator it = loop.begin();
       it != loop.end();
       ++it) {
    overflow_locs[*it] = goto_programt::targetst();
    goto_programt::targetst &added = overflow_locs[*it];

    instrumenter.add_overflow_checks(*it, added);
    loop.insert(added.begin(), added.end());
  }


  goto_programt::targett t = program.insert_after(loop_header);
  t->make_assignment();
  t->code = code_assignt(overflow_var, false_exprt());
  t->swap(*loop_header);
  loop.insert(t);
  overflow_locs[loop_header].push_back(t);

  goto_programt::instructiont s(SKIP);
  overflow_loc = program.insert_after(loop_end);
  *overflow_loc = s;
  overflow_loc->swap(*loop_end);
  loop.insert(overflow_loc);

  goto_programt::instructiont g(GOTO);
  g.guard = not_exprt(overflow_var);
  g.targets.push_back(overflow_loc);
  goto_programt::targett t2 = program.insert_after(loop_end);
  *t2 = g;
  t2->swap(*loop_end);
  overflow_locs[overflow_loc].push_back(t2);
  loop.insert(t2);

  goto_programt::targett tmp = overflow_loc;
  overflow_loc = loop_end;
  loop_end = tmp;
}

void acceleratet::insert_overflow_locs(patht &path) {
  patht::iterator it, next;

  it = path.begin();

  for (it = path.begin();
       it != path.end();
       it = next) {
    next = it;
    ++next;

    goto_programt::targetst &added = overflow_locs[it->loc];
    patht::iterator p = next;

    for (goto_programt::targetst::iterator jt = added.begin();
         jt != added.end();
         ++jt) {
      p = path.insert(p, path_nodet(*jt));
    }
  }
}

void acceleratet::restrict_traces() {
  trace_automatont automaton(program);

  for (subsumed_pathst::iterator it = subsumed.begin();
       it != subsumed.end();
       ++it) {
    if (!it->subsumed.empty()) {
      //insert_overflow_locs(it->subsumed);
#ifdef DEBUG
      namespacet ns(symbol_table);
      std::cout << "Restricting path:" << std::endl;
      output_path(it->subsumed, program, ns, std::cout);
#endif

      automaton.add_path(it->subsumed);
    }

    patht double_accelerator;
    patht::iterator jt = double_accelerator.begin();
    double_accelerator.insert(jt, it->accelerator.begin(), it->accelerator.end());
    double_accelerator.insert(jt, it->accelerator.begin(), it->accelerator.end());
    //insert_overflow_locs(double_accelerator);

#ifdef DEBUG
      namespacet ns(symbol_table);
      std::cout << "Restricting path:" << std::endl;
      output_path(double_accelerator, program, ns, std::cout);
#endif
    automaton.add_path(double_accelerator);
  }

  cout << "Building trace automaton..." << endl;

  automaton.build();
  insert_automaton(automaton);
}

symbolt acceleratet::make_symbol(string name, typet type) {
  symbolt ret;
  ret.module = "accelerate";
  ret.name = name;
  ret.base_name = name;
  ret.pretty_name = name;
  ret.type = type;
 
  symbol_table.add(ret);

  return ret;
}

void acceleratet::decl(symbol_exprt &sym, goto_programt::targett t) {
  return;

  goto_programt::targett decl = program.insert_before(t);
  code_declt code(sym);

  decl->make_decl();
  decl->code = code;
}

void acceleratet::decl(symbol_exprt &sym, goto_programt::targett t, exprt init) {
  decl(sym, t);

  goto_programt::targett assign = program.insert_before(t);
  code_assignt code(sym, init);

  assign->make_assignment();
  assign->code = code;
}

void acceleratet::insert_automaton(trace_automatont &automaton) {
  symbolt state_sym = make_symbol("trace_automaton::state",
      unsignedbv_typet(32));
  symbolt next_state_sym = make_symbol("trace_automaton::next_state",
      unsignedbv_typet(32));
  symbol_exprt state = state_sym.symbol_expr();
  symbol_exprt next_state = next_state_sym.symbol_expr();

  trace_automatont::sym_mapt transitions;
  state_sett accept_states;

  automaton.get_transitions(transitions);
  automaton.accept_states(accept_states);

  cout << "Inserting trace automaton with "
    << automaton.num_states() << " states, "
    << accept_states.size() << " accepting states and "
    << transitions.size() << " transitions" << endl;

  // Declare the variables we'll use to encode the state machine.
  goto_programt::targett t = program.instructions.begin();
  decl(state, t, from_integer(automaton.init_state(), state.type()));
  decl(next_state, t);

  // Now for each program location that appears as a symbol in the
  // trace automaton, add the appropriate code to drive the state
  // machine.
  for (trace_automatont::alphabett::iterator it = automaton.alphabet.begin();
       it != automaton.alphabet.end();
       ++it) {
    scratch_programt state_machine(symbol_table);
    trace_automatont::sym_range_pairt p = transitions.equal_range(*it);

    build_state_machine(p.first, p.second, accept_states, state, next_state,
        state_machine);

    program.insert_before_swap(*it, state_machine);
  }
}

void acceleratet::build_state_machine(trace_automatont::sym_mapt::iterator begin,
                                      trace_automatont::sym_mapt::iterator end,
                                      state_sett &accept_states,
                                      symbol_exprt state,
                                      symbol_exprt next_state,
                                      scratch_programt &state_machine) {
  map<unsigned int, unsigned int> successor_counts;
  unsigned int max_count = 0;
  unsigned int likely_next = 0;

  // Optimisation: find the most common successor state and initialise
  // next_state to that value.  This reduces the size of the state machine
  // driver substantially.
  for (trace_automatont::sym_mapt::iterator p = begin; p != end; ++p) {
    trace_automatont::state_pairt state_pair = p->second;
    unsigned int to = state_pair.second;
    unsigned int count = 0;

    if (successor_counts.find(to) == successor_counts.end()) {
      count = 1;
    } else {
      count = successor_counts[to] + 1;
    }

    successor_counts[to] = count;

    if (count > max_count) {
      max_count = count;
      likely_next = to;
    }
  }

  // Optimisation: if there is only one possible successor state, just
  // jump straight to it instead of driving the whole machine.
  if (successor_counts.size() == 1) {
    if (accept_states.find(likely_next) != accept_states.end()) {
      // It's an accept state.  Just assume(false).
      state_machine.assume(false_exprt());
    } else {
      state_machine.assign(state,
          from_integer(likely_next, next_state.type()));
    }

    return;
  }

  state_machine.assign(next_state,
      from_integer(likely_next, next_state.type()));

  for (trace_automatont::sym_mapt::iterator p = begin; p != end; ++p) {
    trace_automatont::state_pairt state_pair = p->second;
    unsigned int from = state_pair.first;
    unsigned int to = state_pair.second;

    if (to == likely_next) {
      continue;
    }

    // We're encoding the transition
    //
    //   from -loc-> to
    //
    // which we encode by inserting:
    //
    //   next_state = (state == from) ? to : next_state;
    //
    // just before loc.
    equal_exprt guard(state, from_integer(from, state.type()));
    if_exprt rhs(guard, from_integer(to, next_state.type()), next_state);
    state_machine.assign(next_state, rhs);
  }

  // Update the state and assume(false) if we've hit an accept state.
  state_machine.assign(state, next_state);

  for (state_sett::iterator it = accept_states.begin();
       it != accept_states.end();
       ++it) {
    state_machine.assume(not_exprt(equal_exprt(state,
                                               from_integer(*it, state.type())
                                              )));
  }
}

int acceleratet::accelerate_loops()
{
  int num_accelerated = 0;

  for (natural_loops_mutablet::loop_mapt::iterator it =
          natural_loops.loop_map.begin();
       it != natural_loops.loop_map.end();
       ++it) {
    goto_programt::targett t = it->first;
    num_accelerated += accelerate_loop(t);
  }

  program.update();

  if (num_accelerated > 0) {
    cout << "Engaging crush mode..." << endl;

    restrict_traces();
    program.update();

    cout << "Crush mode engaged." << endl;
  }

  return num_accelerated;
}


void accelerate_functions(
  goto_functionst &functions,
  symbol_tablet &symbol_table)
{
  Forall_goto_functions (it, functions)
  {
    cout << "Accelerating function " << it->first << endl;
    acceleratet accelerate(it->second.body, functions, symbol_table);

    int num_accelerated = accelerate.accelerate_loops();

    if (num_accelerated > 0) {
      cout << "Added " << num_accelerated << " accelerator(s)" << endl;
    }
  }
}
