/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_TRACE_AUTOMATON_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_TRACE_AUTOMATON_H

#include "path.h"

#include <goto-programs/goto_program.h>

#include <map>
#include <vector>
#include <set>
#include <iosfwd>

typedef unsigned int statet;
typedef std::set<statet> state_sett;

class automatont
{
 public:
  automatont():
    init_state(no_state),
    num_states(0)
  {
  }

  statet add_state();
  void add_trans(statet s, goto_programt::targett a, statet t);

  bool is_accepting(statet s)
  {
    return accept_states.find(s)!=accept_states.end();
  }

  void set_accepting(statet s)
  {
    accept_states.insert(s);
  }

  void move(statet s, goto_programt::targett a, state_sett &t);
  void move(state_sett &s, goto_programt::targett a, state_sett &t);

  void reverse(goto_programt::targett epsilon);
  void trim();

  std::size_t count_transitions();

  void output(std::ostream &str) const;

  void clear()
  {
    transitions.clear();
    accept_states.clear();
    num_states=0;
  }

  void swap(automatont &that)
  {
    transitions.swap(that.transitions);
    accept_states.swap(that.accept_states);
    num_states=that.num_states;
    init_state=that.init_state;
  }

  static const statet no_state;

// protected:
  typedef std::multimap<goto_programt::targett, statet> transitionst;
  typedef std::pair<transitionst::iterator, transitionst::iterator>
    transition_ranget;
  typedef std::vector<transitionst> transition_tablet;

  statet init_state;
  unsigned num_states;
  transition_tablet transitions;
  state_sett accept_states;
};

class trace_automatont
{
 public:
  explicit trace_automatont(goto_programt &_goto_program):
    goto_program(_goto_program)
  {
    build_alphabet(goto_program);
    init_nta();

    epsilon=goto_program.instructions.end();
    epsilon++; // TODO: This is illegal.
  }

  void add_path(patht &path);

  void build();

  statet init_state()
  {
    return dta.init_state;
  }

  void accept_states(state_sett &states)
  {
    states.insert(dta.accept_states.begin(), dta.accept_states.end());
  }

  typedef std::pair<statet, statet> state_pairt;
  typedef std::multimap<goto_programt::targett, state_pairt> sym_mapt;
  typedef std::pair<sym_mapt::iterator, sym_mapt::iterator> sym_range_pairt;

  void get_transitions(sym_mapt &transitions);

  unsigned num_states()
  {
    return dta.num_states;
  }

  typedef std::set<goto_programt::targett> alphabett;
  alphabett alphabet;

 protected:
  void build_alphabet(goto_programt &program);
  void init_nta();

  bool in_alphabet(goto_programt::targett t)
  {
    return alphabet.find(t)!=alphabet.end();
  }

  void pop_unmarked_dstate(state_sett &s);

  void determinise();
  void epsilon_closure(state_sett &s);

  void minimise();
  void reverse();

  statet add_dstate(state_sett &s);
  statet find_dstate(state_sett &s);
  void add_dtrans(state_sett &s, goto_programt::targett a, state_sett &t);

  typedef std::map<state_sett, statet> state_mapt;

  goto_programt &goto_program;
  goto_programt::targett epsilon;
  std::vector<state_sett> unmarked_dstates;
  state_mapt dstates;

  automatont nta;
  automatont dta;
};

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_TRACE_AUTOMATON_H
