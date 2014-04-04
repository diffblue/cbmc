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
  goto_programt::targett back_jump;
  int num_accelerated = 0;
  natural_loops_mutablet::natural_loopt &loop =
    natural_loops.loop_map[loop_header];

  back_jump = find_back_jump(loop_header);

  goto_programt::instructiont skip(SKIP);
  program.insert_before_swap(loop_header, skip);

  goto_programt::targett new_inst = loop_header;
  ++new_inst;

  loop.insert(new_inst);

  enumerating_loop_accelerationt acceleration(symbol_table, goto_functions,
      program, loop, loop_header, accelerate_limit);

  path_acceleratort accelerator;

  while (acceleration.accelerate(accelerator)) {
    subsumed_patht inserted(accelerator.path);

    insert_accelerator(loop_header, back_jump, accelerator, inserted);
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
}

void acceleratet::restrict_traces() {
  trace_automatont automaton(program);

  for (subsumed_pathst::iterator it = subsumed.begin();
       it != subsumed.end();
       ++it) {
    automaton.add_path(it->subsumed);

    patht double_accelerator;
    patht::iterator jt = double_accelerator.begin();
    double_accelerator.insert(jt, it->accelerator.begin(), it->accelerator.end());
    double_accelerator.insert(jt, it->accelerator.begin(), it->accelerator.end());
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

void acceleratet::build_state_machine(trace_automatont::sym_mapt::iterator p,
                                      trace_automatont::sym_mapt::iterator end,
                                      state_sett &accept_states,
                                      symbol_exprt state,
                                      symbol_exprt next_state,
                                      scratch_programt &state_machine) {
  for ( ; p != end; ++p) {
    trace_automatont::state_pairt state_pair = p->second;
    unsigned int from = state_pair.first;
    unsigned int to = state_pair.second;

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
