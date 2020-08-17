/// \file
/// \author Diffblue Ltd.
///
/// A simple NFA implementation.
///
/// This was created for use in the util/edit_distance.h functionality, which
/// in turn is used in util/cmdline.h for suggesting spelling corrections when
/// a user mistypes a command line option. Because of this the implementation
/// wasn’t done with performance in mind and is probably unsuitable as-is for
/// other purposes where performance does matter.

#ifndef CPROVER_UTIL_NFA_H
#define CPROVER_UTIL_NFA_H

#include <algorithm>
#include <cstddef>
#include <fstream>
#include <iosfwd>
#include <iterator>
#include <unordered_map>
#include <unordered_set>
#include <vector>

/// Very simple NFA implementation
/// Not super performant, but should be good enough for our purposes
template <typename T>
struct nfat
{
  using state_labelt = std::size_t;
  /// A state is a set of possibly active transitions.
  /// The automaton itself is stateless, it just contains
  /// the state transitions.
  struct statet
  {
  private:
    std::unordered_set<state_labelt> possible_states;

  public:
    friend struct nfat;

    bool contains(state_labelt state_label) const
    {
      return possible_states.count(state_label) != 0;
    }
  };

  nfat() = default;

  /// Add a transition from "from" to "to" exactly when "when" is consumed
  void add_transition(state_labelt from, T when, state_labelt to)
  {
    resize_if_necessary(from, to);
    transitions[from].when[when].insert(to);
  }

  /// Add a transition from "from" to "to" when any input is consumed
  /// This is handled a special case so not all inputs need to be enumerated
  /// for arbitrary transitions
  void add_arbitrary_transition(state_labelt from, state_labelt to)
  {
    resize_if_necessary(from, to);
    transitions[from].arbitrary.insert(to);
  }

  /// Add a transition from "from" to "to" that doesn’t consume input
  void add_epsilon_transition(state_labelt from, state_labelt to)
  {
    resize_if_necessary(from, to);
    transitions[from].epsilon.insert(to);
  }

  statet initial_state(state_labelt initial) const
  {
    statet result{};
    result.possible_states.insert(initial);
    follow_epsilon_transitions(result);
    return result;
  }

  statet next_state(const statet &current, const T &input) const
  {
    statet new_state{};
    for(const auto label : current.possible_states)
    {
      const auto &transition = transitions[label];
      const auto it = transition.when.find(input);
      if(it != transition.when.end())
      {
        for(const auto result_state : it->second)
        {
          new_state.possible_states.insert(result_state);
        }
      }
      for(const auto result_state : transition.arbitrary)
      {
        new_state.possible_states.insert(result_state);
      }
    }
    follow_epsilon_transitions(new_state);
    return new_state;
  }

  /// Write the automaton structure to out in graphviz dot format.
  /// Meant for debugging.
  void dump_automaton_dot_to(std::ostream &out) const
  {
    out << "digraph {\n";
    for(state_labelt from = 0; from < transitions.size(); ++from)
    {
      for(const auto to : transitions[from].arbitrary)
      {
        out << 'S' << from << " -> S" << to << "[label=\"*\"]\n";
      }
      for(const auto to : transitions[from].epsilon)
      {
        out << 'S' << from << " -> S" << to << u8"[label=\"ε\"]\n";
      }
      for(const auto &pair : transitions[from].when)
      {
        const auto &in = pair.first;
        const auto &tos = pair.second;
        for(const auto to : tos)
        {
          out << 'S' << from << " -> S" << to << "[label=\"(" << in << ")\"]\n";
        }
      }
    }
    out << "}\n";
  }

private:
  void resize_if_necessary(state_labelt from, state_labelt to)
  {
    const auto min_size = std::max(from, to) + 1;
    if(transitions.size() < min_size)
    {
      transitions.resize(min_size);
    }
  }

  void follow_epsilon_transitions(statet &state) const
  {
    std::vector<state_labelt> new_states{};
    do
    {
      new_states.clear();
      for(const auto from : state.possible_states)
      {
        for(const auto to : transitions[from].epsilon)
        {
          if(!state.contains(to))
          {
            new_states.push_back(to);
          }
        }
      }
      std::copy(
        new_states.begin(),
        new_states.end(),
        std::inserter(state.possible_states, state.possible_states.end()));
    } while(!new_states.empty());
  }

  struct transitiont
  {
    std::unordered_set<state_labelt> epsilon;
    std::unordered_set<state_labelt> arbitrary;
    std::unordered_map<T, std::unordered_set<state_labelt>> when;
  };

  std::vector<transitiont> transitions;
};

#endif // CPROVER_UTIL_NFA_H
