/*******************************************************************\

Module: State of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com
        Alex Horn, alex.horn@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_PATH_SYMEX_STATE_H
#define CPROVER_PATH_SYMEX_STATE_H

#include "locs.h"
#include "var_map.h"
#include "path_symex_history.h"

class path_symex_statet
{
public:
  inline path_symex_statet(
    var_mapt &_var_map,
    const locst &_locs,
    path_symex_historyt &_path_symex_history):
    var_map(_var_map),
    locs(_locs),
    branches(),
    branches_restore(0),
    shared_vars(),
    threads(),
    inside_atomic_section(false),
    history(_path_symex_history),
    unwinding_map(),
    recursion_map(),
    current_thread(0),
    no_thread_interleavings(0),
    depth(0)
  {
  }

  // eagerly copy all fields including vectors etc.
  path_symex_statet(const path_symex_statet& other):
    var_map(other.var_map),
    locs(other.locs),
    branches(other.branches),
    branches_restore(other.branches_restore),
    shared_vars(other.shared_vars),
    threads(other.threads),
    inside_atomic_section(other.inside_atomic_section),
    history(other.history),
    unwinding_map(other.unwinding_map),
    recursion_map(other.recursion_map),
    current_thread(other.current_thread),
    no_thread_interleavings(other.no_thread_interleavings),
    depth(other.depth)
  {
  }

  static path_symex_statet lazy_copy(const path_symex_statet& other)
  {
    // allow compiler to use RVO
    return path_symex_statet(
      other.var_map,
      other.locs,
      other.branches,
      other.inside_atomic_section,
      other.history,
      other.current_thread,
      other.no_thread_interleavings,
      other.depth);
  }

  // These are tied to a particular var_map
  // and a particular program.
  var_mapt &var_map;
  const locst &locs;

  // use symbolic execution to repopulate composite fields

  // TODO: consider std::bitset or chaining to shrink state size
  typedef std::vector<bool> branchest;
  branchest branches;

  // restored state up to strictly less than this index
  branchest::size_type branches_restore;

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

  inline bool is_lazy() const
  {
    return branches_restore < branches.size();
  }

  // returns branch direction that should be taken
  bool restore_branch()
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
  // initialize composite fields to be empty
  path_symex_statet(
    var_mapt &_var_map,
    const locst &_locs,
    const branchest &_branches,
    bool _inside_atomic_section,
    path_symex_step_reft _history,
    unsigned _current_thread,
    unsigned _no_thread_interleavings,
    unsigned _depth):
    var_map(_var_map),
    locs(_locs),
    branches(_branches),
    branches_restore(0),
    shared_vars(/* lazy */),
    threads(/* lazy */),
    inside_atomic_section(_inside_atomic_section),
    history(_history),
    unwinding_map(/* lazy */),
    recursion_map(/* lazy */),
    current_thread(_current_thread),
    no_thread_interleavings(_no_thread_interleavings),
    depth(_depth)
  {
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
