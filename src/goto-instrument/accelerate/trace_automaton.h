#ifndef TRACE_AUTOMATON_H
#define TRACE_AUTOMATON_H

#include "path.h"

#include <goto-programs/goto_program.h>

#include <map>
#include <vector>
#include <set>

typedef unsigned int statet;
typedef std::set<statet> state_sett;

class automatont {
 public:
  automatont() :
    num_states(0)
  {
  }

  statet add_state();
  void add_trans(statet s, goto_programt::targett a, statet t);

  bool is_accepting(statet s) {
    return accept_states.find(s) != accept_states.end();
  }

  void set_accepting(statet s) {
    accept_states.insert(s);
  }

  void move(statet s, goto_programt::targett a, state_sett &t);
  void move(state_sett &s, goto_programt::targett a, state_sett &t);

  statet init_state;

 //protected:
  typedef std::multimap<goto_programt::targett, statet> transitionst;
  typedef std::pair<transitionst::iterator, transitionst::iterator> transition_ranget;
  typedef std::vector<transitionst> transition_tablet;

  statet num_states;
  transition_tablet transitions;
  state_sett accept_states;
};

class trace_automatont {
 public:
  trace_automatont(goto_programt &_goto_program) :
    goto_program(_goto_program)
  {
    build_alphabet(goto_program);
    init_nta();

    epsilon = goto_program.instructions.end();
    epsilon++;
  }

  void add_path(patht &path);

  void build();

  int init_state() {
    return dta.init_state;
  }

  void accept_states(state_sett &states) {
    states.insert(dta.accept_states.begin(), dta.accept_states.end());
  }

  typedef std::pair<statet, statet> state_pairt;
  typedef std::multimap<goto_programt::targett, state_pairt> sym_mapt;
  typedef std::pair<sym_mapt::iterator, sym_mapt::iterator> sym_range_pairt;

  void get_transitions(sym_mapt &transitions);


  typedef std::set<goto_programt::targett> alphabett;
  alphabett alphabet;

 protected:
  void build_alphabet(goto_programt &program);
  void init_nta();

  bool in_alphabet(goto_programt::targett t) {
    return alphabet.find(t) != alphabet.end();
  }

  state_sett &pop_unmarked_dstate();

  void determinise();
  void epsilon_closure(state_sett &s);

  statet add_dstate(state_sett &s);
  statet find_dstate(state_sett &s);
  void add_dtrans(state_sett &s, goto_programt::targett a, state_sett &t);

  void build_sym_map();

  typedef std::map<state_sett, statet> state_mapt;

  goto_programt &goto_program;
  goto_programt::targett epsilon;
  std::vector<state_sett> unmarked_dstates;
  state_mapt dstates;

  automatont nta;
  automatont dta;

  sym_mapt sym_map;
};

#endif // TRACE_AUTOMATON_H
