#include "trace_automaton.h"
#include "path.h"

/*
 * Build the trace automaton alphabet.
 *
 * The alphabet is the set of basic block headers, i.e. the
 * location of the first instruction in the program, along
 * with any location with more than one predecessor.
 */
void trace_automatont::build_alphabet(goto_programt &program) {
  alphabett seen;

  // The first location is a basic block header...
  alphabet.insert(program.instructions.begin());

  // Now loop over each instruction in the program & see which successors
  // the instruction has.  If we encounter a successor we've already seen,
  // that location has multiple predecessors & so is a basic block header.
  for (goto_programt::targett it = program.instructions.begin();
       it != program.instructions.end();
       ++it) {
    goto_programt::targetst succs;

    program.get_successors(it, succs);

    for (goto_programt::targetst::iterator jt = succs.begin();
         jt != succs.end();
         ++jt) {
      if (seen.find(*jt) != seen.end()) {
        // We've seen this location before.  Add it to the alphabet.
        alphabet.insert(*jt);
      }

      seen.insert(*jt);
    }
  }
}

void trace_automatont::init_nta() {
  nta.init_state = nta.add_state();

  for (alphabett::iterator it = alphabet.begin();
       it != alphabet.end();
       ++it) {
    goto_programt::targett &t = const_cast<goto_programt::targett&>(*it);
    nta.add_trans(nta.init_state, t, nta.init_state);
  }
}

/*
 * Add a path to the trace automaton.
 */
void trace_automatont::add_path(patht &path) {
  statet state;

  state = nta.add_state();
  nta.add_trans(nta.init_state, epsilon, state);

  for (patht::iterator it = path.begin();
       it != path.end();
       ++it) {
    goto_programt::targett l = it->loc;

    if (in_alphabet(l)) {
      statet new_state = nta.add_state();
      nta.add_trans(state, l, new_state);
      state = new_state;
    }
  }

  nta.set_accepting(state);
}

/*
 * Use the subset construction (cf. the Dragon book)
 * to convert a nondeterministic trace automaton (NTA) to
 * a deterministic one (DTA).
 */
void trace_automatont::determinise() {
  state_sett init_states;

  init_states.insert(nta.init_state);
  epsilon_closure(init_states);

  dta.init_state = add_dstate(init_states);

  while (!unmarked_dstates.empty()) {
    state_sett &t = pop_unmarked_dstate();

    // For each symbol a such that there is a transition
    //
    // s -a-> s'
    //
    // for some s in t, find the states that are reachable
    // using a-transitions and add them as a new state.
    for (alphabett::iterator it = alphabet.begin();
         it != alphabet.end();
         ++it) {
      state_sett u;

      nta.move (t, *it, u);
      epsilon_closure(u);

      add_dstate(u);
      add_dtrans(t, *it, u);
    }
  }
}

state_sett &trace_automatont::pop_unmarked_dstate() {
  state_sett &ret = unmarked_dstates.back();
  unmarked_dstates.pop_back();

  return ret;
}

/*
 * Calculate the epsilon closure of a set of states in a NTA.
 */
void trace_automatont::epsilon_closure(state_sett &states) {
  std::vector<statet> queue(states.size());

  // Initialise -- fill queue with states.
  for (state_sett::iterator it = states.begin();
       it != states.end();
       ++it) {
    queue.push_back(*it);
  }

  // Take epsilon transitions until we can take no more.
  while (!queue.empty()) {
    statet state = queue.back();
    state_sett next_states;

    queue.pop_back();

    nta.move(state, epsilon, next_states);

    // Check if we've arrived at any fresh states.  If so, recurse on them.
    for (state_sett::iterator it = next_states.begin();
         it != next_states.end();
         ++it) {
      if (states.find(*it) != states.end()) {
        // This is a new state.  Add it to the state set & enqueue it.
        states.insert(*it);
        queue.push_back(*it);
      }
    }
  }
}



/*
 * Create a new (unmarked) state in the DTA if the state has not been added
 * before.
 */
statet trace_automatont::add_dstate(state_sett &s) {
  statet state_num = find_dstate(s);

  if (state_num >= 0) {
    // We've added this state before.  Don't need to do it again.
    return state_num;
  }

  state_num = dta.add_state();
  dstates[s] = state_num;
  unmarked_dstates.push_back(s);

  for (state_sett::iterator it = s.begin();
       it != s.end();
       ++it) {
    if (nta.is_accepting(*it)) {
      dta.set_accepting(state_num);
      break;
    }
  }

  return state_num;
}

statet trace_automatont::find_dstate(state_sett &s) {
  state_mapt::iterator it = dstates.find(s);

  if (it == dstates.end()) {
    return -1;
  } else {
    return it->second;
  }
}

/*
 * Add a new state.
 */
statet automatont::add_state() {
  transitionst trans;
  transitions.push_back(trans);

  return num_states++;
}

/*
 * Add the transition s -a-> t.
 */
void automatont::add_trans(statet s, goto_programt::targett a, statet t) {
  assert(s < transitions.size());
  transitionst &trans = transitions[s];

  trans.insert(std::pair<goto_programt::targett, statet>(a, t));
}

/*
 * Add a transition to the DTA.
 */
void trace_automatont::add_dtrans(state_sett &s,
                                 goto_programt::targett a,
                                 state_sett &t) {
  statet sidx = find_dstate(s);
  statet tidx = find_dstate(t);

  assert(sidx >= 0);
  assert(tidx >= 0);

  dta.add_trans(sidx, a, tidx);
}

void automatont::move(statet s, goto_programt::targett a, state_sett &t) {
  assert(s >= 0);
  assert(s < transitions.size());

  transitionst &trans = transitions[s];

  transition_ranget range = trans.equal_range(a);

  for(transitionst::iterator it = range.first;
      it != range.second;
      ++it) {
    t.insert(it->second);
  }
}

void automatont::move(state_sett &s, goto_programt::targett a, state_sett &t) {
  for (state_sett::iterator it = s.begin();
       it != s.end();
       ++it) {
    move(*it, a, t);
  }
}

bool automatont::is_accepting(statet s) {
  return accept_states.find(s) != accept_states.end();
}

void automatont::set_accepting(statet s) {
  accept_states.insert(s);
}
