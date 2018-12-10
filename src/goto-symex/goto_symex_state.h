/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#ifndef CPROVER_GOTO_SYMEX_GOTO_SYMEX_STATE_H
#define CPROVER_GOTO_SYMEX_GOTO_SYMEX_STATE_H

#include <memory>
#include <unordered_set>

#include <analyses/dirty.h>
#include <analyses/local_safe_pointers.h>

#include <util/invariant.h>
#include <util/guard.h>
#include <util/std_expr.h>
#include <util/ssa_expr.h>
#include <util/make_unique.h>

#include <pointer-analysis/value_set.h>
#include <goto-programs/goto_function.h>

#include "renaming_level.h"
#include "symex_target_equation.h"

// central data structure: state
class goto_symex_statet final
{
public:
  goto_symex_statet();
  ~goto_symex_statet();

  /// \brief Fake "copy constructor" that initializes the `symex_target` member
  explicit goto_symex_statet(
    const goto_symex_statet &other,
    symex_target_equationt *const target)
    : goto_symex_statet(other) // NOLINT
  {
    symex_target = target;
  }

  /// contains symbols that are minted during symbolic execution, such as
  /// dynamically created objects etc. The names in this table are needed
  /// for error traces even after symbolic execution has finished.
  symbol_tablet symbol_table;

  /// distance from entry
  unsigned depth;

  guardt guard;
  symex_targett::sourcet source;
  symex_target_equationt *symex_target;

  // we remember all L1 renamings
  std::set<irep_idt> l1_history;

  symex_level0t level0;
  symex_level1t level1;
  symex_level2t level2;

  // Map L1 names to (L2) constants
  std::map<irep_idt, exprt> propagation;
  void output_propagation_map(std::ostream &);

  enum levelt { L0=0, L1=1, L2=2 };

  // performs renaming _up to_ the given level
  void rename(exprt &expr, const namespacet &ns, levelt level=L2);
  void rename(
    typet &type,
    const irep_idt &l1_identifier,
    const namespacet &ns,
    levelt level=L2);

  void assignment(
    ssa_exprt &lhs, // L0/L1
    const exprt &rhs,  // L2
    const namespacet &ns,
    bool rhs_is_simplified,
    bool record_value,
    bool allow_pointer_unsoundness=false);

  // undoes all levels of renaming
  void get_original_name(exprt &expr) const;
  void get_original_name(typet &type) const;
protected:
  void rename_address(exprt &expr, const namespacet &ns, levelt level);

  void set_l0_indices(ssa_exprt &expr, const namespacet &ns);
  void set_l1_indices(ssa_exprt &expr, const namespacet &ns);
  void set_l2_indices(ssa_exprt &expr, const namespacet &ns);

  // only required for value_set.assign
  void get_l1_name(exprt &expr) const;

  // this maps L1 names to (L2) types
  typedef std::unordered_map<irep_idt, typet> l1_typest;
  l1_typest l1_types;

public:
  std::unordered_map<irep_idt, local_safe_pointerst> safe_pointers;

  // uses level 1 names, and is used to
  // do dereferencing
  value_sett value_set;

  class goto_statet
  {
  public:
    unsigned depth;
    symex_level2t::current_namest level2_current_names;
    value_sett value_set;
    guardt guard;
    symex_targett::sourcet source;
    std::map<irep_idt, exprt> propagation;
    unsigned atomic_section_id;
    std::unordered_map<irep_idt, local_safe_pointerst> safe_pointers;
    unsigned total_vccs, remaining_vccs;

    explicit goto_statet(const goto_symex_statet &s)
      : depth(s.depth),
        level2_current_names(s.level2.current_names),
        value_set(s.value_set),
        guard(s.guard),
        source(s.source),
        propagation(s.propagation),
        atomic_section_id(s.atomic_section_id),
        safe_pointers(s.safe_pointers),
        total_vccs(s.total_vccs),
        remaining_vccs(s.remaining_vccs)
    {
    }

    // the below replicate levelt2 member functions
    void level2_get_variables(
      std::unordered_set<ssa_exprt, irep_hash> &vars) const
    {
      for(const auto &pair : level2_current_names)
        vars.insert(pair.second.first);
    }

    unsigned level2_current_count(const irep_idt &identifier) const
    {
      const auto it = level2_current_names.find(identifier);
      return it==level2_current_names.end()?0:it->second.second;
    }
  };

  explicit goto_symex_statet(const goto_statet &s)
    : depth(s.depth),
      guard(s.guard),
      source(s.source),
      propagation(s.propagation),
      safe_pointers(s.safe_pointers),
      value_set(s.value_set),
      atomic_section_id(s.atomic_section_id),
      total_vccs(s.total_vccs),
      remaining_vccs(s.remaining_vccs)
  {
    level2.current_names = s.level2_current_names;
  }

  // gotos
  typedef std::list<goto_statet> goto_state_listt;
  typedef std::map<goto_programt::const_targett, goto_state_listt>
    goto_state_mapt;

  // stack frames -- these are used for function calls and
  // for exceptions
  struct framet
  {
    // function calls
    irep_idt function_identifier;
    goto_state_mapt goto_state_map;
    symex_targett::sourcet calling_location;

    goto_programt::const_targett end_of_function;
    exprt return_value = nil_exprt();
    bool hidden_function = false;

    symex_renaming_levelt::current_namest old_level1;

    std::set<irep_idt> local_objects;

    // exceptions
    std::map<irep_idt, goto_programt::targett> catch_map;

    // loop and recursion unwinding
    struct loop_infot
    {
      unsigned count = 0;
      bool is_recursion = false;
    };
    std::unordered_map<irep_idt, loop_infot> loop_iterations;
  };

  typedef std::vector<framet> call_stackt;

  call_stackt &call_stack()
  {
    PRECONDITION(source.thread_nr < threads.size());
    return threads[source.thread_nr].call_stack;
  }

  const call_stackt &call_stack() const
  {
    PRECONDITION(source.thread_nr < threads.size());
    return threads[source.thread_nr].call_stack;
  }

  framet &top()
  {
    PRECONDITION(!call_stack().empty());
    return call_stack().back();
  }

  const framet &top() const
  {
    PRECONDITION(!call_stack().empty());
    return call_stack().back();
  }

  framet &new_frame() { call_stack().push_back(framet()); return top(); }
  void pop_frame() { call_stack().pop_back(); }
  const framet &previous_frame() { return *(--(--call_stack().end())); }

  void print_backtrace(std::ostream &) const;

  // threads
  unsigned atomic_section_id;
  typedef std::pair<unsigned, std::list<guardt> > a_s_r_entryt;
  typedef std::list<guardt> a_s_w_entryt;
  std::unordered_map<ssa_exprt, a_s_r_entryt, irep_hash> read_in_atomic_section;
  std::unordered_map<ssa_exprt, a_s_w_entryt, irep_hash>
    written_in_atomic_section;

  unsigned total_vccs, remaining_vccs;

  struct threadt
  {
    goto_programt::const_targett pc;
    guardt guard;
    call_stackt call_stack;
    std::map<irep_idt, unsigned> function_frame;
    unsigned atomic_section_id = 0;
  };

  std::vector<threadt> threads;

  bool l2_thread_read_encoding(ssa_exprt &expr, const namespacet &ns);
  bool l2_thread_write_encoding(const ssa_exprt &expr, const namespacet &ns);

  bool record_events;
  incremental_dirtyt dirty;

  goto_programt::const_targett saved_target;

  /// \brief This state is saved, with the PC pointing to the target of a GOTO
  bool has_saved_jump_target;

  /// \brief This state is saved, with the PC pointing to the next instruction
  /// of a GOTO
  bool has_saved_next_instruction;

  /// \brief Should the additional validation checks be run?
  bool run_validation_checks;

private:
  /// \brief Dangerous, do not use
  ///
  /// Copying a state S1 to S2 risks S2 pointing to a deallocated
  /// symex_target_equationt if S1 (and the symex_target_equationt that its
  /// `symex_target` member points to) go out of scope. If your class has a
  /// goto_symex_statet member and needs a copy constructor, copy instances
  /// of this class using the public two-argument copy constructor
  /// constructor to ensure that the copy points to an allocated
  /// symex_target_equationt. The two-argument copy constructor uses this
  /// private copy constructor as a delegate.
  goto_symex_statet(const goto_symex_statet &other) = default;
};

#endif // CPROVER_GOTO_SYMEX_GOTO_SYMEX_STATE_H
