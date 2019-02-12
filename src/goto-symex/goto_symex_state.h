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

#include <util/invariant.h>
#include <util/guard.h>
#include <util/std_expr.h>
#include <util/ssa_expr.h>
#include <util/make_unique.h>

#include <pointer-analysis/value_set.h>
#include <goto-programs/goto_function.h>

#include "renaming_level.h"
#include "symex_target_equation.h"

/// Container for data that varies per program point, e.g. the constant
/// propagator state, when state needs to branch. This is copied out of
/// goto_symex_statet at a control-flow fork and then back into it at a
/// control-flow merge.
class goto_statet
{
public:
  /// Distance from entry
  unsigned depth = 0;

  symex_level2t level2;

  /// Uses level 1 names, and is used to do dereferencing
  value_sett value_set;

  // A guard is a particular condition that has to pass for an instruction
  // to be executed. The easiest example is an if/else: each instruction along
  // the if branch will be guarded by the condition of the if (and if there
  // is an else branch then instructions on it will be guarded by the negation
  // of the condition of the if).
  guardt guard{true_exprt{}};

  symex_targett::sourcet source;

  // Map L1 names to (L2) constants. Values will be evicted from this map
  // when they become non-constant. This is used to propagate values that have
  // been worked out to only have one possible value.
  //
  // "constants" can include symbols, but only in the context of an address-of
  // op (i.e. &x can be propagated), and an address-taken thing should only be
  // L1.
  std::map<irep_idt, exprt> propagation;

  void output_propagation_map(std::ostream &);

  /// Threads
  unsigned atomic_section_id = 0;

  unsigned total_vccs = 0;
  unsigned remaining_vccs = 0;

  /// Constructors
  explicit goto_statet(const class goto_symex_statet &s);
  explicit goto_statet(const symex_targett::sourcet &_source) : source(_source)
  {
  }
};

// stack frames -- these are used for function calls and
// for exceptions
struct framet
{
  // gotos
  using goto_state_listt = std::list<goto_statet>;

  // function calls
  irep_idt function_identifier;
  std::map<goto_programt::const_targett, goto_state_listt> goto_state_map;
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

  explicit framet(symex_targett::sourcet _calling_location)
    : calling_location(std::move(_calling_location))
  {
  }
};

/// Central data structure: state.

/// The state is a persistent data structure that symex maintains as it
/// executes. As we walk over each instruction, state will be updated reflecting
/// their effects until a branch occurs (such as an if), where parts of the
/// state will be copied into a \ref goto_statet, stored in a map for later
/// reference and then merged again (via merge_goto) once it reaches a
/// control-flow graph convergence.
class goto_symex_statet final : public goto_statet
{
public:
  explicit goto_symex_statet(const symex_targett::sourcet &);
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

  symex_target_equationt *symex_target;

  // we remember all L1 renamings
  std::set<irep_idt> l1_history;

  symex_level0t level0;
  symex_level1t level1;

  // Symex renaming levels.
  enum levelt { L0=0, L1=1, L2=2 };

  /// Rewrites symbol expressions in \ref exprt, applying a suffix to each
  /// symbol reflecting its most recent version, which differs depending on
  /// which level you requested. Each level also updates its predecessors, so
  /// a L1 rename will update L1 and L0. A L2 will update L2, L1 and L0.
  ///
  /// What happens at each level:
  ///     L0. Applies a suffix giving the current thread number. (Excludes
  ///         guards, dynamic objects and anything not considered thread-local)
  ///     L1. Applies a suffix giving the current loop iteration or recursive
  ///         function invocation.
  ///     L2. Applies a suffix giving the generation of this variable.
  ///
  /// Renaming will not increment any of these values, just update the
  /// expression with them. Levels matter when reading a variable, for
  /// example: reading the value of x really means reading the particular x
  /// symbol for this thread (L0 renaming, if applicable), the most recent
  /// instance of x (L1 renaming), and the most recent write to x (L2 renaming).
  ///
  /// The above example after being renamed could look like this: 'x!0@0#42'.
  /// That states it's the 42nd generation of this variable, on the first
  /// thread, in the first frame.
  ///
  /// A full explanation of SSA (which is why we do this renaming) is in
  /// the SSA section of background-concepts.md.
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

protected:
  void rename_address(exprt &expr, const namespacet &ns, levelt level);

  /// Update level 0 values.
  void set_l0_indices(ssa_exprt &expr, const namespacet &ns);

  /// Update level 0 and 1 values.
  void set_l1_indices(ssa_exprt &expr, const namespacet &ns);

  /// Update level 0, 1 and 2 values.
  void set_l2_indices(ssa_exprt &expr, const namespacet &ns);

  // this maps L1 names to (L2) types
  typedef std::unordered_map<irep_idt, typet> l1_typest;
  l1_typest l1_types;

public:
  // gotos
  typedef std::list<goto_statet> goto_state_listt;

  // guards
  static irep_idt guard_identifier()
  {
    static irep_idt id = "goto_symex::\\guard";
    return id;
  }

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

  framet &new_frame()
  {
    call_stack().emplace_back(source);
    return top();
  }

  void pop_frame() { call_stack().pop_back(); }

  const framet &previous_frame() { return *(--(--call_stack().end())); }

  void print_backtrace(std::ostream &) const;

  // threads
  typedef std::pair<unsigned, std::list<guardt> > a_s_r_entryt;
  typedef std::list<guardt> a_s_w_entryt;
  std::unordered_map<ssa_exprt, a_s_r_entryt, irep_hash> read_in_atomic_section;
  std::unordered_map<ssa_exprt, a_s_w_entryt, irep_hash>
    written_in_atomic_section;

  struct threadt
  {
    goto_programt::const_targett pc;
    guardt guard{true_exprt{}};
    call_stackt call_stack;
    std::map<irep_idt, unsigned> function_frame;
    unsigned atomic_section_id = 0;
  };

  std::vector<threadt> threads;

  bool l2_thread_read_encoding(ssa_exprt &expr, const namespacet &ns);
  bool l2_thread_write_encoding(const ssa_exprt &expr, const namespacet &ns);

  bool record_events;

  // Local variables are considered 'dirty' if they've had an address taken and
  // therefore may be referred to by a pointer.
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

inline goto_statet::goto_statet(const class goto_symex_statet &s)
  : depth(s.depth),
    level2(s.level2),
    value_set(s.value_set),
    guard(s.guard),
    source(s.source),
    propagation(s.propagation),
    atomic_section_id(s.atomic_section_id),
    total_vccs(s.total_vccs),
    remaining_vccs(s.remaining_vccs)
{
}

#endif // CPROVER_GOTO_SYMEX_GOTO_SYMEX_STATE_H
