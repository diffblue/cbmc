/*******************************************************************\

Module: Witnesses for Traces and Proofs

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Witnesses for Traces and Proofs

#ifndef CPROVER_GOTO_PROGRAMS_GRAPHML_WITNESS_H
#define CPROVER_GOTO_PROGRAMS_GRAPHML_WITNESS_H

#include <xmllang/graphml.h>

#include <goto-symex/symex_target_equation.h>

#include "goto_trace.h"

class graphml_witnesst
{
public:
  explicit graphml_witnesst(const namespacet &_ns)
    : ns(_ns)
  {
  }

  void operator()(const goto_tracet &goto_trace);
  void operator()(const symex_target_equationt &equation);

  const graphmlt &graph()
  {
    return graphml;
  }

protected:
  const namespacet &ns;
  graphmlt graphml;

  void remove_l0_l1(exprt &expr);
  std::string convert_assign_rec(
    const irep_idt &identifier,
    const code_assignt &assign);

  template <typename T>
  static void hash_combine(std::size_t &seed, const T &v)
  {
    std::hash<T> hasher;
    seed ^= hasher(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
  }

  template <typename S, typename T>
  struct pair_hash // NOLINT(readability/identifiers)
  {
    std::size_t operator()(const std::pair<S, T> &v) const
    {
      std::size_t seed = 0;
      hash_combine(seed, v.first);
      hash_combine(seed, v.second);
      return seed;
    }
  };
  std::unordered_map<
    std::pair<unsigned int, const irept::dt *>,
    std::string,
    pair_hash<unsigned int, const irept::dt *>>
    cache;
};

#endif // CPROVER_GOTO_PROGRAMS_GRAPHML_WITNESS_H
