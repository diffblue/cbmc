#include "trace_automaton.h"
#include "path.h"

void trace_automatont::build() {
  build_alphabet();

  for (unsigned int i = 0; i < paths.size(); i++) {
    init_state[i] = 0;
    accept_state[i] = -1;
  }

  add_state(init_state);
  add_state(accept_state);

  unsigned int num_states = 0;

  while (num_states != states.size()) {
    num_states = states.size();

    for (unsigned int i = 0; i < num_states; i++) {
      statet &state = states[i];

      for (alphabett::iterator it = alphabet.begin();
           it != alphabet.end();
           ++it) {
        goto_programt::targett &sym = const_cast<goto_programt::targett &>(*it);
        statet next_state;

        step(state, sym, next_state);
        add_transition(state, sym, next_state);
      }
    }
  }

  // Done!
}

void trace_automatont::step(statet &state, goto_programt::targett &sym,
    statet &next_state) {
#if 0
  unsigned int state_idx = 0;

  for (unsigned int i = 0; i < states.size(); i++) {
    patht &path = paths[i];
    int idx = state[i];

    if (sym == path[idx]) {
      if (idx + 1 == path.size()) {
        next_state = accept_state;
        return;
      }

      next_state[i] = idx + 1;
    } else {
      // sym is not the next symbol we were expecting...
      // Find out how far along the path we could have gotten.
      next_state[i] = max_index(path, idx, sym);
    }
  }
#endif
}

int trace_automatont::find_state(statet &state) {
  state_mapt::iterator it = state_map.find(state);

  if (it == state_map.end()) {
    return add_state(state);
  }

  return it->second;
}

int trace_automatont::add_state(statet &state) {
  int ret = states.size();
  state_map[state] = ret;
  states.push_back(state);

  return ret;
}

int trace_automatont::max_index(patht &path, int idx,
    goto_programt::targett &sym) {
  return 0;
}

void trace_automatont::build_alphabet() {
}

void trace_automatont::add_transition(statet &from, goto_programt::targett &sym,
    statet &to) {
}
