/// \file
/// \author Diffblue Ltd.
///
/// Loosely based on this blog post:
///   http://blog.notdot.net/2010/07/Damn-Cool-Algorithms-Levenshtein-Automata
/// Provides a way to compute edit distance between two strings
///
/// No conversion to DFA or other optimisations are done here because for our
/// use case (i.e. suggestions for errors in command line specifications) this
/// is fast enough without them.

#ifndef CPROVER_UTIL_EDIT_DISTANCE_H
#define CPROVER_UTIL_EDIT_DISTANCE_H

#include "nfa.h"

#include <cstddef>
#include <string>

#include <util/optional.h>

/// Simple automaton that can detect whether a string can be transformed into
/// another with a limited number of deletions, insertions or substitutions.
/// Not a very fast implementation, but should be good enough for small strings.
struct levenshtein_automatont
{
private:
  nfat<char> nfa;
  using state_labelt = nfat<char>::state_labelt;
  std::vector<state_labelt> final_states;

public:
  levenshtein_automatont(
    const std::string &string,
    std::size_t allowed_errors = 2);

  bool matches(const std::string &string) const;
  optionalt<std::size_t> get_edit_distance(const std::string &string) const;

  void dump_automaton_dot_to(std::ostream &out)
  {
    nfa.dump_automaton_dot_to(out);
  };
};

#endif // CPROVER_UTIL_EDIT_DISTANCE_H
