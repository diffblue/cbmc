/*******************************************************************\

Module: State of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com
        Alex Horn, alex.horn@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_PATH_SYMEX_STATE_H
#define CPROVER_PATH_SYMEX_STATE_H

#include <algorithm>

#include "locs.h"
#include "var_map.h"
#include "path_symex_history.h"

// These variables may be defined in this header file only because
// it is (transitively) included by many essential path-symex files.
// In addition, since these variables determine how states are
// handled, it makes sense to define them in this header file.
#define PATH_SYMEX_LAZY_STATE
#define PATH_SYMEX_FORK

// This flag is particularly useful for regression testing purposes.
//
// If PATH_SYMEX_LAZY_BRANCH is undefined, then branches are always
// recorded and the control logic in get_branches() is bypassed. But
// the output of path_search() should be identical in this setting;
// otherwise, the assumptions about GOTO programs or the history
// data structure should be revisited.
#define PATH_SYMEX_LAZY_BRANCH

// check POSIX-compliance
#ifdef PATH_SYMEX_FORK
#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
#include <unistd.h>
#include <sys/types.h>
#else
#error Cannot define PATH_SYMEX_FORK on non-POSIX systems
#endif
#endif

class path_symex_statet
{
public:
  // use symbolic execution to repopulate composite fields

  // TODO: consider std::bitset or chaining to shrink state size
  typedef std::vector<bool> branchest;

  // if _branches.empty(), then initial state; otherwise, lazy state

  // \post: pc() is the entry point to the program under scrutiny
  path_symex_statet(
    var_mapt &_var_map,
    const locst &_locs,
    path_symex_step_reft _history,
    const branchest &_branches):
    var_map(_var_map),
    locs(_locs),
    shared_vars(),
    threads(),
    inside_atomic_section(),
    history(_history),
    unwinding_map(),
    recursion_map(),
    branches(_branches),
    branches_restore(0),
    current_thread(0),
    no_thread_interleavings(0),
    depth(0)
  {
    path_symex_statet::threadt &thread=add_thread();
    thread.pc=locs.entry_loc; // reset its PC
  }

  // like initial state except that branches are copied from "other"
  // and history will be 'nil'
  static path_symex_statet lazy_copy(path_symex_statet& other)
  {
    // allow compiler to use RVO
    return path_symex_statet(
      other.var_map,
      other.locs,
      path_symex_step_reft(),
      other.get_branches());
  }

  // These are tied to a particular var_map
  // and a particular program.
  var_mapt &var_map;
  const locst &locs;

  // the value of a variable
  struct var_statet
  {
    // it's a given explicit value or a symbol with given identifier
    exprt value;
    symbol_exprt ssa_symbol;
    
    // for uninterpreted functions or arrays we maintain an index set
    typedef std::set<exprt> index_sett;
    index_sett index_set;

    var_statet():
      value(nil_exprt()),
      ssa_symbol(irep_idt())
    {
    }
  };
  
  // the values of the shared variables
  typedef std::vector<var_statet> var_valt;
  var_valt shared_vars;
  
  // procedure frame
  struct framet
  {
    irep_idt current_function;
    loc_reft return_location;
    exprt return_lhs;
    var_valt saved_local_vars;
  };

  // call stack  
  typedef std::vector<framet> call_stackt;
  
  // the state of a thread
  struct threadt
  {
  public:
    loc_reft pc;    
    call_stackt call_stack; // the call stack
    var_valt local_vars; // thread-local variables
    bool active;
    
    threadt():active(true)
    {
    }
  };
  
  typedef std::vector<threadt> threadst;
  threadst threads;

  // warning: reference is not stable
  var_statet &get_var_state(const var_mapt::var_infot &var_info);
  
  bool inside_atomic_section;
  
  inline unsigned get_current_thread() const
  {
    return current_thread;
  }

  inline void set_current_thread(unsigned _thread)
  {
    current_thread=_thread;
  }
  
  goto_programt::const_targett get_instruction() const;

  // branch taken case
  inline void record_true_branch()
  {
    branches.push_back(true);
  }

  // branch not taken case
  inline void record_false_branch()
  {
    branches.push_back(false);
  }

  inline bool is_lazy() const
  {
    return branches_restore < branches.size();
  }

  // returns branch direction that should be taken
  inline bool restore_branch()
  {
    assert(is_lazy());
    return branches[branches_restore++];
  }

  inline bool is_executable() const
  {
    return !threads.empty() &&
           threads[current_thread].active;
  }

  // execution history
  path_symex_step_reft history;
  
  // adds an entry to the history
  void record_step();

  // like record_step() except that branch decision is also recorded
  void record_branch_step(bool taken);

  // various state transformers
  
  inline threadt &add_thread()
  {
    threads.resize(threads.size()+1);
    return threads.back();
  }
  
  inline void disable_current_thread()
  {
    threads[current_thread].active=false;
  }

  inline loc_reft pc() const
  {
    return threads[current_thread].pc;
  }

  inline void next_pc()
  {
    threads[current_thread].pc.increase();
  }

  inline void set_pc(loc_reft new_pc)
  {
    threads[current_thread].pc=new_pc;
  }
  
  // output  
  void output(std::ostream &out) const;
  void output(const threadt &thread, std::ostream &out) const;

  // instantiate expressions with propagation
  inline exprt read(const exprt &src)
  {
    return read(src, true);
  }
  
  // instantiate without constant propagation
  inline exprt read_no_propagate(const exprt &src)
  {
    return read(src, false);
  }

  exprt dereference_rec(const exprt &src, bool propagate);

  std::string array_index_as_string(const exprt &) const;
  
  inline unsigned get_no_thread_interleavings() const
  {
    return no_thread_interleavings;
  }
  
  inline unsigned get_depth() const
  {
    return depth;
  }
  
  bool is_feasible(class decision_proceduret &) const;

  bool check_assertion(class decision_proceduret &);

  // counts how many times we have executed backwards edges
  typedef std::map<loc_reft, unsigned> unwinding_mapt;
  unwinding_mapt unwinding_map;

  // similar for recursive function calls
  typedef std::map<irep_idt, unsigned> recursion_mapt;
  recursion_mapt recursion_map;

protected:
  branchest branches;
  branchest::size_type branches_restore;

  // On first call, O(N) where N is the length of the execution path
  // leading to this state. Subsequent calls run in constant time.
  const branchest& get_branches()
  {
    if(!branches.empty() || history.is_nil())
      return branches;

    // Contrarily, suppose this state is lazy. Since we did not
    // return above, branches.empty(). By definition of is_lazy(),
    // branches_restore must have been a negative number. Since
    // its type is unsigned, however, this is impossible.
    assert(!is_lazy());

    path_symex_step_reft step_ref=history;
    assert(!step_ref.is_nil());
    loc_reft next_loc_ref=pc();
    for(;;)
    {
      if(step_ref.is_nil())
        break;

      const loct &loc=locs[step_ref->pc];
      if(loc.target->is_goto())
      {
        branches.push_back(loc.branch_target==next_loc_ref);
        assert(branches.back() || step_ref->pc.next_loc()==next_loc_ref);
      }

      next_loc_ref=step_ref->pc;
      step_ref=step_ref->predecessor;
    }

    // preserve non-laziness of this state (see first assertion)
    branches_restore=branches.size();

    // TODO: add "path_symex_step::branch_depth" field so we can
    // reserve() the right capacity of vector and avoid reverse().
    std::reverse(branches.begin(), branches.end());

    return branches;
  }

  unsigned current_thread;
  unsigned no_thread_interleavings;
  unsigned depth;

  exprt read(
    const exprt &src,
    bool propagate);

  exprt instantiate_rec(
    const exprt &src,
    bool propagate);

  exprt instantiate_rec_address(
    const exprt &src,
    bool propagate);

  exprt read_symbol_member_index(
    const exprt &src,
    bool propagate);
};

path_symex_statet initial_state(
  var_mapt &var_map,
  const locst &locs,
  path_symex_historyt &);
  
#endif
