#include <utility>
#include <iostream>

#include "trace_automaton.h"
#include "path.h"

//#define DEBUG

void trace_automatont::build() {
#ifdef DEBUG
  std::cout << "NTA:" << std::endl;
  nta.output(std::cout);
#endif

  determinise();
  //minimise();

#ifdef DEBUG
  std::cout << "DTA:" << std::endl;
  dta.output(std::cout);
#endif
}

/*
 * Build the trace automaton alphabet.
 *
 * The alphabet is the set of distinguishing points, i.e. the
 * successors of any location with multiple successors.
 */
void trace_automatont::build_alphabet(goto_programt &program) {
  for (goto_programt::targett it = program.instructions.begin();
       it != program.instructions.end();
       ++it) {
    goto_programt::targetst succs;

    program.get_successors(it, succs);

    if (succs.size() > 1) {
      alphabet.insert(succs.begin(), succs.end());
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

#ifdef DEBUG
  std::cout << "Adding path: ";
#endif

  for (patht::iterator it = path.begin();
       it != path.end();
       ++it) {
    goto_programt::targett l = it->loc;
#ifdef DEBUG
      std::cout << ", " << l->location_number << ":" << l->location;
#endif

    if (in_alphabet(l)) {
#ifdef DEBUG
      std::cout << "(*) ";
#endif

      statet new_state = nta.add_state();
      nta.add_trans(state, l, new_state);
      state = new_state;
    }
  }

#ifdef DEBUG
  std::cout << std::endl;

  std::cout << "Final state: " << state << std::endl;
#endif

  nta.set_accepting(state);
}

/*
 * Use the subset construction (cf. the Dragon book)
 * to convert a nondeterministic trace automaton (NTA) to
 * a deterministic one (DTA).
 */
void trace_automatont::determinise() {
#ifdef DEBUG
  std::cout << "Determinising automaton with " << nta.num_states <<
    " states and " << nta.accept_states.size() << " accept states and " 
    << nta.count_transitions() << " transitions" << endl;
#endif

  dstates.clear();
  unmarked_dstates.clear();
  dta.clear();

  state_sett init_states;
  init_states.insert(nta.init_state);
  epsilon_closure(init_states);

#ifdef DEBUG
  std::cout << "There are " << init_states.size() << " init states" << endl;
#endif

  dta.init_state = add_dstate(init_states);

  while (!unmarked_dstates.empty()) {
    state_sett t;
    pop_unmarked_dstate(t);
    assert(find_dstate(t) != no_state);


    // For each symbol a such that there is a transition
    //
    // s -a-> s'
    //
    // for some s in t, find the states that are reachable
    // using a-transitions and add them as a new state.
    for (alphabett::iterator it = alphabet.begin();
         it != alphabet.end();
         ++it) {
      if (*it == epsilon) {
        continue;
      }

      state_sett u;

      nta.move (t, *it, u);
      epsilon_closure(u);

      add_dstate(u);
      add_dtrans(t, *it, u);
    }
  }

  dta.trim();

#ifdef DEBUG
  std::cout << "Produced DTA with " << dta.num_states <<
    " states and " << dta.accept_states.size() << " accept states and "
    << dta.count_transitions() << " transitions" << std::endl;
#endif
}

void trace_automatont::pop_unmarked_dstate(state_sett &s) {
  s = unmarked_dstates.back();
  unmarked_dstates.pop_back();
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
      if (states.find(*it) == states.end()) {
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

  if (state_num != no_state) {
    // We've added this state before.  Don't need to do it again.
    return state_num;
  }

  state_num = dta.add_state();
  dstates[s] = state_num;
  unmarked_dstates.push_back(s);

  assert(dstates.find(s) != dstates.end());

  for (state_sett::iterator it = s.begin();
       it != s.end();
       ++it) {
    if (nta.is_accepting(*it)) {
#ifdef DEBUG
      std::cout << "NTA state " << *it << " is accepting, so accepting DTA state " <<
        state_num << std::endl;
#endif

      dta.set_accepting(state_num);
      break;
    }
  }

  return state_num;
}

statet trace_automatont::find_dstate(state_sett &s) {
  state_mapt::iterator it = dstates.find(s);

  if (it == dstates.end()) {
    return no_state;
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

  trans.insert(std::make_pair(a, t));
}

/*
 * Add a transition to the DTA.
 */
void trace_automatont::add_dtrans(state_sett &s,
                                 goto_programt::targett a,
                                 state_sett &t) {
  statet sidx = find_dstate(s);
  statet tidx = find_dstate(t);

  assert(sidx != no_state);
  assert(tidx != no_state);

  dta.add_trans(sidx, a, tidx);
}

void automatont::move(statet s, goto_programt::targett a, state_sett &t) {
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

void trace_automatont::get_transitions(sym_mapt &transitions) {
  automatont::transition_tablet &dtrans = dta.transitions;

  for (unsigned int i = 0; i < dtrans.size(); ++i) {
    automatont::transitionst &dta_transitions = dtrans[i];

    for (automatont::transitionst::iterator it = dta_transitions.begin();
         it != dta_transitions.end();
         ++it) {
      goto_programt::targett l = it->first;
      unsigned int j = it->second;

      // We have a transition: i -l-> j.
      state_pairt state_pair(i, j);
      transitions.insert(std::make_pair(l, state_pair));
    }
  }
}

void automatont::reverse(goto_programt::targett epsilon) {
  transition_tablet old_table;
  statet new_init;

  old_table.swap(transitions);

  for (unsigned int i = 0; i < old_table.size(); i++) {
    transitions.push_back(transitionst());
  }

  if (accept_states.size() == 0) {
    num_states = 0;
    return;
  } else if (accept_states.size() == 1) {
    new_init = *(accept_states.begin());
  } else {
    // More than one accept state.  Introduce a new state with
    // epsilon transitions to each accept state.
    new_init = add_state();

    for (state_sett::iterator it = accept_states.begin();
         it != accept_states.end();
         ++it) {
      add_trans(new_init, epsilon, *it);
    }
  }

  std::cout << "Reversing automaton, old init=" << init_state << ", new init="
    << new_init << ", old accept=" << *(accept_states.begin()) << "/" << accept_states.size()
    << " new accept=" << init_state << std::endl;

  accept_states.clear();
  set_accepting(init_state);

  init_state = new_init;

  for (unsigned int i = 0; i < old_table.size(); i++) {
    transitionst &trans = old_table[i];

    for (transitionst::iterator it = trans.begin();
         it != trans.end();
         ++it) {
      goto_programt::targett l = it->first;
      unsigned int j = it->second;

      // There was a transition i -l-> j, so add a transition
      // j -l-> i.
      add_trans(j, l, i);
    }
  }
}

void automatont::trim() {
  state_sett reachable;
  state_sett new_states;

  reachable.insert(init_state);
  new_states.insert(init_state);

  do {
    state_sett tmp;

    for (state_sett::iterator it = new_states.begin();
         it != new_states.end();
         ++it) {
      transitionst &trans = transitions[*it];

      for (transitionst::iterator jt = trans.begin();
           jt != trans.end();
           ++jt) {
        unsigned int j = jt->second;

        if (reachable.find(j) == reachable.end()) {
          reachable.insert(j);
          tmp.insert(j);
        }
      }
    }

    tmp.swap(new_states);
  } while (!new_states.empty());

  for (unsigned int i = 0; i < num_states; i++) {
    if (reachable.find(i) == reachable.end()) {
      transitions[i] = transitionst();
      accept_states.erase(i);
    }
  }
}

// Produce a minimal DTA using Brzozowski's algorithm.
void trace_automatont::minimise() {
  nta.reverse(epsilon);
  determinise();

  nta.swap(dta);
  nta.reverse(epsilon);
  determinise();
}

void automatont::output(std::ostream &str) {
  str << "Init: " << init_state << std::endl;

  str << "Accept states: ";

  for (state_sett::iterator it = accept_states.begin();
       it != accept_states.end();
       ++it) {
    str << *it << " ";
  }

  str << std::endl;

  for (unsigned int i = 0; i < transitions.size(); ++i) {
    for (transitionst::iterator it = transitions[i].begin();
         it != transitions[i].end();
         ++it) {
      goto_programt::targett l = it->first;
      statet j = it->second;

      str << i << " -- " << l->location_number << " --> " << j << std::endl;
    }
  }
}

unsigned int automatont::count_transitions() {
  unsigned int ret = 0;

  for (transition_tablet::iterator it = transitions.begin();
       it != transitions.end();
       ++it) {
    ret += it->size();
  }

  return ret;
}
