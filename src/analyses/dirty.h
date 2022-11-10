/*******************************************************************\

Module: Variables whose address is taken

Author: Daniel Kroening

Date: March 2013

\*******************************************************************/

/// \file
/// Variables whose address is taken

#ifndef CPROVER_ANALYSES_DIRTY_H
#define CPROVER_ANALYSES_DIRTY_H

#include <util/invariant.h>
#include <util/std_expr.h>

#include <goto-programs/goto_functions.h>

#include <unordered_set>

/// Dirty variables are ones which have their address taken so we can't
/// reliably work out where they may be assigned and are also considered shared
/// state in the presence of multi-threading.
class dirtyt
{
private:
  void die_if_uninitialized() const
  {
    INVARIANT(
      initialized,
      "Uninitialized dirtyt. This dirtyt was constructed using the default "
      "constructor and not subsequently initialized using "
      "dirtyt::build().");
  }

public:
  bool initialized;

  /// \post dirtyt objects that are created through this constructor are not
  /// safe to use. If you copied a dirtyt (for example, by adding an object
  /// that owns a dirtyt to a container and then copying it back out), you will
  /// need to re-initialize the dirtyt by calling dirtyt::build().
  dirtyt() : initialized(false)
  {
  }

  explicit dirtyt(const goto_programt &goto_program) : initialized(false)
  {
    build(goto_program);
    initialized = true;
  }

  explicit dirtyt(const goto_functionst &goto_functions) : initialized(false)
  {
    build(goto_functions);
    // build(g_funs) responsible for setting initialized to true, since
    // it is public and can be called independently
  }

  void output(std::ostream &out) const;

  bool operator()(const irep_idt &id) const
  {
    die_if_uninitialized();
    return dirty.find(id) != dirty.end();
  }

  bool operator()(const symbol_exprt &expr) const
  {
    die_if_uninitialized();
    return operator()(expr.get_identifier());
  }

  const std::unordered_set<irep_idt> &get_dirty_ids() const
  {
    die_if_uninitialized();
    return dirty;
  }

  void add_function(const goto_programt &goto_program)
  {
    build(goto_program);
    initialized = true;
  }

  void build(const goto_functionst &goto_functions)
  {
    // dirtyts should not be initialized twice
    PRECONDITION(!initialized);
    for(const auto &gf_entry : goto_functions.function_map)
      build(gf_entry.second.body);
    initialized = true;
  }

protected:
  void build(const goto_programt &);

  // variables whose address is taken
  std::unordered_set<irep_idt> dirty;
  void search_other(const goto_programt::instructiont &instruction);
  void find_dirty(const exprt &expr);
  void find_dirty_address_of(const exprt &expr);
};

inline std::ostream &operator<<(std::ostream &out, const dirtyt &dirty)
{
  dirty.output(out);
  return out;
}

/// Wrapper for dirtyt that permits incremental population, ensuring each
/// function is analysed exactly once.
class incremental_dirtyt
{
public:
  void populate_dirty_for_function(
    const irep_idt &id,
    const goto_programt &goto_program);

  bool operator()(const irep_idt &id) const
  {
    return dirty(id);
  }

  bool operator()(const symbol_exprt &expr) const
  {
    return dirty(expr);
  }

private:
  dirtyt dirty;
  std::unordered_set<irep_idt> dirty_processed_functions;
};

#endif // CPROVER_ANALYSES_DIRTY_H
