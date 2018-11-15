/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Renaming levels

#ifndef CPROVER_GOTO_SYMEX_RENAMING_LEVEL_H
#define CPROVER_GOTO_SYMEX_RENAMING_LEVEL_H

#include <map>
#include <unordered_set>

#include <util/irep.h>
#include <util/ssa_expr.h>

struct renaming_levelt
{
  virtual ~renaming_levelt() = default;

  typedef std::map<irep_idt, std::pair<ssa_exprt, unsigned>> current_namest;
  current_namest current_names;

  unsigned current_count(const irep_idt &identifier) const
  {
    const auto it = current_names.find(identifier);
    return it == current_names.end() ? 0 : it->second.second;
  }

  void increase_counter(const irep_idt &identifier)
  {
    PRECONDITION(current_names.find(identifier) != current_names.end());
    ++current_names[identifier].second;
  }

  void get_variables(std::unordered_set<ssa_exprt, irep_hash> &vars) const
  {
    for(const auto &pair : current_names)
      vars.insert(pair.second.first);
  }
};

// level 0 -- threads!
// renaming built for one particular interleaving
struct symex_level0t : public renaming_levelt
{
  void
  operator()(ssa_exprt &ssa_expr, const namespacet &ns, unsigned thread_nr);

  symex_level0t() = default;
  ~symex_level0t() override = default;
};

// level 1 -- function frames
// this is to preserve locality in case of recursion

struct symex_level1t : public renaming_levelt
{
  void operator()(ssa_exprt &ssa_expr);

  void restore_from(const current_namest &other)
  {
    auto it = current_names.begin();
    for(const auto &pair : other)
    {
      while(it != current_names.end() && it->first < pair.first)
        ++it;
      if(it == current_names.end() || pair.first < it->first)
        current_names.insert(it, pair);
      else if(it != current_names.end())
      {
        PRECONDITION(it->first == pair.first);
        it->second = pair.second;
        ++it;
      }
    }
  }

  symex_level1t() = default;
  ~symex_level1t() override = default;
};

// level 2 -- SSA
struct symex_level2t : public renaming_levelt
{
  symex_level2t() = default;
  ~symex_level2t() override = default;
};

#endif // CPROVER_GOTO_SYMEX_RENAMING_LEVEL_H
