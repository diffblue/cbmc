/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_GOTO_SYMEX_STATE_H
#define CPROVER_GOTO_SYMEX_GOTO_SYMEX_STATE_H

#include <cassert>
#include <unordered_set>

#include <util/guard.h>
#include <util/std_expr.h>
#include <util/ssa_expr.h>

#include <pointer-analysis/value_set.h>
#include <goto-programs/goto_functions.h>

#include "symex_target.h"

// central data structure: state
class goto_symex_statet
{
public:
  goto_symex_statet();

  // distance from entry
  unsigned depth;

  bool is_start_thread;
  guardt guard;
  symex_targett::sourcet source;
  symex_targett *symex_target;

  void initialize(const goto_functionst &goto_functions);

  // we have a two-level renaming

  typedef std::map<irep_idt, irep_idt> original_identifierst;

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
      assert(current_names.find(identifier)!=current_names.end());
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
          assert(it->first==ito->first);
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

  typedef enum { L0=0, L1=1, L2=2 } levelt;

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
    bool record_value);

  // what to propagate
  bool constant_propagation(const exprt &expr) const;
  bool constant_propagation_reference(const exprt &expr) const;

  // undoes all levels of renaming
  void get_original_name(exprt &expr) const;
  void get_original_name(typet &type) const;
protected:
  void rename_address(exprt &expr, const namespacet &ns, levelt level);

  void set_ssa_indices(ssa_exprt &expr, const namespacet &ns, levelt level=L2);
  // only required for value_set.assign
  void get_l1_name(exprt &expr) const;

  // this maps L1 names to (L2) types
  typedef std::unordered_map<irep_idt, typet, irep_id_hash> l1_typest;
  l1_typest l1_types;

public:
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
    propagationt propagation;
    unsigned atomic_section_id;

    explicit goto_statet(const goto_symex_statet &s):
      depth(s.depth),
      level2_current_names(s.level2.current_names),
      value_set(s.value_set),
      guard(s.guard),
      propagation(s.propagation),
      atomic_section_id(s.atomic_section_id)
    {
    }

    // the below replicate levelt2 member functions
    void level2_get_variables(std::unordered_set<ssa_exprt, irep_hash> &vars) const
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

  // gotos
  typedef std::list<goto_statet> goto_state_listt;
  typedef std::map<goto_programt::const_targett, goto_state_listt> goto_state_mapt;

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
    typedef std::unordered_map<irep_idt, loop_infot, irep_id_hash>
      loop_iterationst;
    loop_iterationst loop_iterations;
  };

  typedef std::vector<framet> call_stackt;

  inline call_stackt &call_stack()
  {
    assert(source.thread_nr<threads.size());
    return threads[source.thread_nr].call_stack;
  }

  inline const call_stackt &call_stack() const
  {
    assert(source.thread_nr<threads.size());
    return threads[source.thread_nr].call_stack;
  }

  inline framet &top()
  {
    assert(!call_stack().empty());
    return call_stack().back();
  }

  inline const framet &top() const
  {
    assert(!call_stack().empty());
    return call_stack().back();
  }

  inline framet &new_frame() { call_stack().push_back(framet()); return top(); }
  inline void pop_frame() { call_stack().pop_back(); }
  inline const framet &previous_frame() { return *(--(--call_stack().end())); }

  // threads
  unsigned atomic_section_id;
  typedef std::pair<unsigned, std::list<guardt> > a_s_r_entryt;
  typedef std::unordered_map<ssa_exprt, a_s_r_entryt, irep_hash> read_in_atomic_sectiont;
  typedef std::list<guardt> a_s_w_entryt;
  typedef std::unordered_map<ssa_exprt, a_s_w_entryt, irep_hash> written_in_atomic_sectiont;
  read_in_atomic_sectiont read_in_atomic_section;
  written_in_atomic_sectiont written_in_atomic_section;

  class threadt
  {
  public:
    goto_programt::const_targett pc;
    guardt guard;
    call_stackt call_stack;
    std::map<irep_idt, unsigned> function_frame;
    unsigned atomic_section_id;
    unsigned priority;

    threadt():
      atomic_section_id(0),
      priority(0)
    {
    }
  };

  typedef std::vector<threadt> threadst;
  threadst threads;

  bool l2_thread_read_encoding(ssa_exprt &expr, const namespacet &ns);
  bool l2_thread_write_encoding(const ssa_exprt &expr, const namespacet &ns);

  void switch_to_thread(unsigned t);
  bool record_events;
};

#endif // CPROVER_GOTO_SYMEX_GOTO_SYMEX_STATE_H
