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
  typedef std::set<irep_idt> l1_historyt;
  l1_historyt l1_history;

  struct renaming_levelt
  {
    virtual ~renaming_levelt() { }

    typedef std::map<irep_idt, std::pair<ssa_exprt, unsigned> > current_namest;
    current_namest current_names;

    unsigned current_count(const irep_idt &identifier) const
    {
      current_namest::const_iterator it=
        current_names.find(identifier);
      return it==current_names.end()?0:it->second.second;
    }

    void increase_counter(const irep_idt &identifier)
    {
      PRECONDITION(current_names.find(identifier) != current_names.end());
      ++current_names[identifier].second;
    }

    void get_variables(std::unordered_set<ssa_exprt, irep_hash> &vars) const
    {
      for(current_namest::const_iterator it=current_names.begin();
          it!=current_names.end();
          it++)
        vars.insert(it->second.first);
    }
  };

  // level 0 -- threads!
  // renaming built for one particular interleaving
  struct level0t:public renaming_levelt
  {
    void operator()(
      ssa_exprt &ssa_expr,
      const namespacet &ns,
      unsigned thread_nr);

    level0t() { }
    virtual ~level0t() { }
  } level0;

  // level 1 -- function frames
  // this is to preserve locality in case of recursion

  struct level1t:public renaming_levelt
  {
    void operator()(ssa_exprt &ssa_expr);

    void restore_from(const current_namest &other)
    {
      current_namest::iterator it=current_names.begin();
      for(current_namest::const_iterator
          ito=other.begin();
          ito!=other.end();
          ++ito)
      {
        while(it!=current_names.end() && it->first<ito->first)
          ++it;
        if(it==current_names.end() || ito->first<it->first)
          current_names.insert(it, *ito);
        else if(it!=current_names.end())
        {
          PRECONDITION(it->first == ito->first);
          it->second=ito->second;
          ++it;
        }
      }
    }

    level1t() { }
    virtual ~level1t() { }
  } level1;

  // level 2 -- SSA

  struct level2t:public renaming_levelt
  {
    level2t() { }
    virtual ~level2t() { }
  } level2;

  // this maps L1 names to (L2) constants
  class propagationt
  {
  public:
    typedef std::map<irep_idt, exprt> valuest;
    valuest values;
    void operator()(exprt &expr);

    void remove(const irep_idt &identifier)
    {
      values.erase(identifier);
    }
  } propagation;

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

  void set_ssa_indices(ssa_exprt &expr, const namespacet &ns, levelt level=L2);
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
    level2t::current_namest level2_current_names;
    value_sett value_set;
    guardt guard;
    symex_targett::sourcet source;
    propagationt propagation;
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
      for(level2t::current_namest::const_iterator
          it=level2_current_names.begin();
          it!=level2_current_names.end();
          it++)
        vars.insert(it->second.first);
    }

    unsigned level2_current_count(const irep_idt &identifier) const
    {
      level2t::current_namest::const_iterator it=
        level2_current_names.find(identifier);
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
  class framet
  {
  public:
    // function calls
    irep_idt function_identifier;
    goto_state_mapt goto_state_map;
    symex_targett::sourcet calling_location;

    goto_programt::const_targett end_of_function;
    exprt return_value;
    bool hidden_function;

    renaming_levelt::current_namest old_level1;

    typedef std::set<irep_idt> local_objectst;
    local_objectst local_objects;

    framet():
      return_value(nil_exprt()),
      hidden_function(false)
    {
    }

    // exceptions
    typedef std::map<irep_idt, goto_programt::targett> catch_mapt;
    catch_mapt catch_map;

    // loop and recursion unwinding
    struct loop_infot
    {
      loop_infot():
        count(0),
        is_recursion(false)
      {
      }

      unsigned count;
      bool is_recursion;
    };
    typedef std::unordered_map<irep_idt, loop_infot> loop_iterationst;
    loop_iterationst loop_iterations;
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

  // threads
  unsigned atomic_section_id;
  typedef std::pair<unsigned, std::list<guardt> > a_s_r_entryt;
  typedef std::unordered_map<ssa_exprt, a_s_r_entryt, irep_hash>
    read_in_atomic_sectiont;
  typedef std::list<guardt> a_s_w_entryt;
  typedef std::unordered_map<ssa_exprt, a_s_w_entryt, irep_hash>
    written_in_atomic_sectiont;
  read_in_atomic_sectiont read_in_atomic_section;
  written_in_atomic_sectiont written_in_atomic_section;

  unsigned total_vccs, remaining_vccs;

  class threadt
  {
  public:
    goto_programt::const_targett pc;
    guardt guard;
    call_stackt call_stack;
    std::map<irep_idt, unsigned> function_frame;
    unsigned atomic_section_id;

    threadt():
      atomic_section_id(0)
    {
    }
  };

  typedef std::vector<threadt> threadst;
  threadst threads;

  bool l2_thread_read_encoding(ssa_exprt &expr, const namespacet &ns);
  bool l2_thread_write_encoding(const ssa_exprt &expr, const namespacet &ns);

  void populate_dirty_for_function(
    const irep_idt &id, const goto_functiont &);

  void switch_to_thread(unsigned t);
  bool record_events;
  incremental_dirtyt dirty;

  goto_programt::const_targett saved_target;

  /// \brief This state is saved, with the PC pointing to the target of a GOTO
  bool has_saved_jump_target;

  /// \brief This state is saved, with the PC pointing to the next instruction
  /// of a GOTO
  bool has_saved_next_instruction;
  bool saved_target_is_backwards;

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
