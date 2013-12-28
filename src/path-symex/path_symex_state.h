/*******************************************************************\

Module: State of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PATH_SYMEX_STATE_H
#define CPROVER_PATH_SYMEX_STATE_H

#if 0
#include <set>

#include <util/expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#endif

#include "locs.h"
#include "var_map.h"
#include "path_symex_history.h"

struct path_symex_statet
{
public:
  inline path_symex_statet(
    var_mapt &_var_map,
    const locst &_locs):
    var_map(_var_map),
    locs(_locs),
    inside_atomic_section(false),
    current_thread(0)
  {
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
    irep_idt identifier;

    var_statet():value(nil_exprt())
    {
    }
  };
  
  // the values of the shared variables
  typedef std::vector<var_statet> var_valt;
  var_valt shared_vars;
  
  // procedure frame
  struct framet
  {
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
    
    threadt()
    {
    }
  };
  
  typedef std::vector<threadt> threadst;
  threadst threads;

  var_statet &get_var_state(const var_mapt::var_infot &var_info)
  {
    var_valt &var_val=
      var_info.is_shared()?shared_vars:threads[current_thread].local_vars;
    if(var_val.size()>=var_info.number) var_val.resize(var_info.number+1);
    return var_val[var_info.number];
  }

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
  
  inline bool is_executable() const
  {
    return !threads.empty();
  }

  inline void swap(path_symex_statet &other)
  {
    threads.swap(other.threads);
    std::swap(inside_atomic_section, other.inside_atomic_section);
    std::swap(current_thread, other.current_thread);
  }
  
  // execution history
  path_symex_historyt history;
  
  // adds an entry to the history
  path_symex_stept &record_step();

  // various state transformers
  
  inline threadt &add_thread()
  {
    threads.resize(threads.size()+1);
    return threads.back();
  }
  
  inline void remove_current_thread()
  {
    threads.erase(threads.begin()+current_thread);
    if(current_thread>threads.size()) current_thread--;
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
  exprt read(const exprt &src);
  
  // instantiate without constant propagation
  exprt read_no_propagate(const exprt &src);

protected:
  unsigned current_thread;

  exprt instantiate_rec(
    const exprt &src,
    const std::string &suffix,
    const typet &suffix_type,
    bool propagate,
    bool is_address);
};

path_symex_statet initial_state(
  var_mapt &var_map,
  const locst &locs);
  
#endif
