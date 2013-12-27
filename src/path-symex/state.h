/*******************************************************************\

Module: State of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_STATE_H
#define CPROVER_STATE_H

#include <set>

#include <util/expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include <path-symex/loc_ref.h>

#include "var_map.h"

struct statet
{
public:
  explicit inline statet(var_mapt &_var_map):
    var_map(_var_map),
    atomic_section_count(0),
    node(NULL),
    current_thread(0),
    context_switches(0)
  {
  }

  // mapping from IDs to numbers  
  var_mapt &var_map;
  
  // the value of a variable
  struct var_statet
  {
    // it's a given explicit value or a symbol with given identifier
    exprt value;
    irep_idt identifier;
    // index of step where variable was last assigned
    unsigned step_number;
    
    var_statet():value(nil_exprt()), step_number(0)
    {
    }
  };
  
  // the values of the shared variables
  typedef std::vector<var_statet> var_valt;
  var_valt shared_vars;

  struct framet
  {
    loc_reft return_location;
    exprt return_lhs;
    var_valt saved_local_vars;
  };
  
  typedef std::vector<framet> call_stackt;
  
  // the state of a thread
  struct threadt
  {
  public:
    bool active;
    loc_reft pc;    
    call_stackt call_stack; // the call stack
    var_valt local_vars; // thread-local variables
    
    threadt():active(true)
    {
    }
  };
  
  typedef std::vector<threadt> threadst;
  threadst threads;
  

  inline unsigned get_current_thread() const {
    return current_thread;
  }

  void set_current_thread(unsigned next_thread) {
    if(next_thread!=current_thread)
      ++context_switches;

    current_thread=next_thread;
  }

  inline unsigned get_context_switches() const {
    return context_switches;
  }


  void get_global_pc(std::vector<std::vector<loc_reft> > &dest) const
  {
    dest.resize(threads.size());
    for(unsigned thr=0; thr<threads.size(); ++thr)
    {
      std::vector<loc_reft>& dest_call_stack=dest[thr];
      const call_stackt& call_stack=threads[thr].call_stack;
      
      if(threads[thr].active)
      {
      	dest_call_stack.resize(call_stack.size()+1);
       	unsigned i=0;
        for(; i<call_stack.size(); ++i)
      	  dest_call_stack[i]= call_stack[i].return_location;
        	dest_call_stack[i]=threads[thr].pc;
      }
      else // we can pretend that the callstack of inactive thread is empty
      	dest_call_stack.push_back(loc_reft()); 
    }
  }

  bool has_active_thread() const
  {
    if(atomic_section_count>0)
      return threads[current_thread].active;

    for(unsigned t=0; t<threads.size(); t++)
      if(threads[t].active) return true;

    return false;
  }
 
  unsigned atomic_section_count;

  var_statet &get_var_state(const var_mapt::var_infot &var_info)
  {
    unsigned n=var_info.number;

    bool shared=var_info.is_shared();

    var_valt &var_val=
      shared ? 
        shared_vars:
        threads[current_thread].local_vars;

    if(var_val.size()<=n) var_val.resize(n+1);
    return var_val[n];
  }

  class stept
  {
  public:
    unsigned thread_nr;
    std::vector<loc_reft> pc_vector;
    exprt guard, ssa_rhs; // constant-propagated
    exprt guard_no_prop, ssa_rhs_no_prop; // not propagated
    exprt lhs;
    symbol_exprt ssa_lhs;
    class nodet *node;
    bool ignore; 
    
    stept():
      guard(nil_exprt()),
      ssa_rhs(nil_exprt()),
      guard_no_prop(nil_exprt()),
      ssa_rhs_no_prop(nil_exprt()),
      lhs(nil_exprt()),
      node(NULL),
      ignore(false)
    {
    }

    void get_pc_vector(statet& state)
    {
      pc_vector.resize(state.threads.size());
      for(unsigned thr=0; thr<state.threads.size(); ++thr)
      {
      	if(state.threads[thr].active)
      	{
          pc_vector[thr]=state.threads[thr].pc;
      	}
    	else // we can pretend that the callstack of inactive thread is empty
	      pc_vector[thr]=loc_reft(); 
      }
    }
    
    inline loc_reft pc() const { return pc_vector[thread_nr]; }  
  };
  

  std::map<unsigned, unsigned> unwind_map;

  class nodet *node;

  typedef std::vector<stept> historyt;
  historyt history;

  bool has_false_guard(historyt::iterator& it)
  {
    it=history.end();

    for(statet::historyt::iterator
          h_it=history.begin();
          h_it!=history.end();
          h_it++) 
    {
      if(h_it->guard.is_false())
      {
        it=h_it;
      }
    }

    return it!=history.end();
  }

  bool shared_accesses(const stept& step, 
					   std::set<exprt>& reads, 
					   std::set<exprt>& writes);

  bool last_shared_accesses(std::set<exprt>& reads, 
					   std::set<exprt>& writes);

  bool shared_accesses(
    const exprt &expr,
    std::set<exprt> &accesses,
    bool record);

  bool shared_accesses(
    const exprt& expr,
    const std::string &suffix,
    std::set<exprt>& accesses,
    bool record);

  // output history as SSA constraints into dest
  void ssa_constraints(class prop_conv_solvert &dest, 
                       nodet* ancestor,
                       std::map<exprt,exprt>& activation,
                       bool prop=true) const;
  

  void ssa_constraints(std::vector<exprt>& constraints, 
                       nodet* ancestor,
                       bool prop=true) const;

  stept &record_step();
  
  void swap(statet &other)
  {
    threads.swap(other.threads);
    shared_vars.swap(other.shared_vars);
    history.swap(other.history);
    std::swap(atomic_section_count, other.atomic_section_count);
    std::swap(current_thread, other.current_thread);
    std::swap(node, other.node);
    assert(&var_map==&other.var_map);
  }
  
  // various state transformers
  
  threadt &add_thread()
  {
    threads.resize(threads.size()+1);
    return threads.back();
  }

  inline loc_reft pc() const { return threads[current_thread].pc; }

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

  // resolve dereferencing
  exprt dereference(const exprt &src);

  // recursive descent for `dereference'
  void dereference_rec(exprt &src);

  // deal with ID_address_of
  void dereference_rec_address_of(exprt &expr);

  bool is_index_member_symbol_if(const exprt &expr);

  // deal with pointer arithmetic
  exprt address_arithmetic(const exprt &expr);

  // construct deref-free expression
  exprt build_reference_to(const exprt &src);

  // construct `object' and `offset' from `expr'
  void build_offset_expr(const exprt& expr, 
                         exprt& object, 
                         exprt& offset, 
                         const std::string &suffix,
                         const typet &original_type);

  // byte_extract according to endianness
  static irep_idt byte_extract_id();

  // remove `#'
  static exprt original_name(const exprt &src);
  
  static bool is_null(const exprt& e);

  exprt ssa_name(const exprt& src, nodet*);
  exprt ssa_eval(const exprt& src, statet::historyt::reverse_iterator h_rit); 
   
  static bool overlap(const std::set<exprt>& a, const std::set<exprt>& b)
  {
    typedef std::set<exprt> expr_sett;

    for(expr_sett::const_iterator
            it=a.begin();
            it!=a.end();
            ++it)
    {
      if(b.find(*it)!=b.end())
            return true;
    }

    return false;
  }

  /* dependencies
    reads:   only with a write of same variable
	writes: with any occurrence of the variable
  */ 		
  static bool independent(
    const std::set<exprt>& reads1,
    const std::set<exprt>& writes1,
    const std::set<exprt>& reads2,
    const std::set<exprt>& writes2)
  {
    return    !overlap(reads2, writes1)
           && !overlap(reads1, writes2)
	   && !overlap(writes1, writes2);
  }

  void show_vcc(
    nodet* ancestor,
    const exprt& start, 
    const exprt& cond,
    bool prop,
    std::ostream &out);

protected:

  unsigned current_thread;
  unsigned context_switches;

  exprt instantiate_rec(
      const exprt &src,   
      const std::string &suffix, 
      const typet &suffix_type,
      bool propagate, 
      bool is_address);
};


class slicert 
 {
 public:
   slicert (const namespacet& __ns,
            statet::historyt& __history):
      ns(__ns),
      history(__history)
   {
     reset_ignore();
   }

   ~slicert()
   {
     reset_ignore();
   }

   void operator()(const exprt& start, const exprt& cond, bool include_guards=true);
   void operator()(statet::historyt::iterator& step);

 protected:
   typedef hash_set_cont<irep_idt, irep_id_hash> symbol_sett;
   symbol_sett depends;
   const namespacet& ns;
   statet::historyt& history;

   void reset_ignore();
   void slice_assignments(bool include_guards=false);
};


statet initial_state(
  var_mapt &var_map,
  class nodest &nodes,
  loc_reft entry_loc,
  nodet* node);

  
#endif
