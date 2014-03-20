#ifndef TRACE_AUTOMATON_H
#define TRACE_AUTOMATON_H

#include "path.h"

#include <goto-programs/goto_program.h>

#include <map>
#include <vector>
#include <set>

class trace_automatont {
 public:
  trace_automatont(goto_programt &_goto_program) :
    goto_program(_goto_program)
  {
  }

  void add_path(patht &path) {
    paths.push_back(path);
  }

  void build();

 protected:
  typedef struct {
    goto_programt::targett sym;
    int from;
    int to;
  } transitiont;

  typedef std::set<transitiont> transitionst;
  typedef std::vector<int> statet;
  typedef std::vector<statet> statest;
  typedef std::map<statet, int> state_mapt;
  typedef std::map<goto_programt::targett, transitionst> transition_mapt;
  typedef std::set<goto_programt::targett> alphabett;

  void build_alphabet();

  int find_state(statet &state);
  int add_state(statet &state);

  void step(statet &state, goto_programt::targett &sym, statet &to);
  void add_transition(statet &from, goto_programt::targett &sym, statet &to);

  int max_index(patht &path, int idx, goto_programt::targett &sym);

  pathst paths;
  statest states;
  state_mapt state_map;
  alphabett alphabet;
  transitionst transitions;
  statet init_state;
  statet accept_state;

  goto_programt &goto_program;
};

#endif // TRACE_AUTOMATON_H
