/*******************************************************************\

Module: Abstract Interpretation (context-sensitive)

Author: Daniel Poetzl, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ANALYSES_AI_CS_H
#define CPROVER_ANALYSES_AI_CS_H

#include <map>
#include <tuple>
#include <stack>
#include <queue>
#include <utility>
#include <iosfwd>

#include <goto-programs/goto_functions.h>
#include <util/config.h>
#include <util/misc_utils.h>
#include <util/cprover_prefix.h>
#include <util/map_one_con.h>
#include <util/numbering.h>
#include <analyses/in_loop.h>

#include "show_analysis.h"

#include "ai_cs_stack.h"

// forward reference
class ai_cs_baset;

// don't use me -- I am just a base class
// please derive from me
class ai_cs_domain_baset
{
public:
  typedef goto_programt::const_targett locationt;

  // The constructor is expected to produce 'false'
  // or 'bottom'
  ai_cs_domain_baset()
  {
  }

  virtual ~ai_cs_domain_baset()
  {
  }

  // how function calls are treated:
  // a) there is an edge from each call site to the function head
  // b) there is an edge from the last instruction (END_FUNCTION) of the
  //    function to the instruction _following_ the call site (this also needs
  // to set the LHS, if applicable)

  // stack:
  // - for call edge: stack at callee
  // - for return edge: stack at callee
  // - for create edge: stack at callee (of create_thread)
  // - other edges: same stack at source and target
  virtual void transform(
    locationt from,
    locationt to,
    const ai_cs_stackt &stack,
    ai_cs_baset &ai,
    const namespacet &ns)=0;

  virtual void output(
    std::ostream &out,
    const ai_cs_baset &ai,
    const namespacet &ns) const
  {
  }
  
  // no states
  virtual void make_bottom()
  {
  }

  // all states
  virtual void make_top()
  {
  }
  
  // also add
  //
  //   bool merge(
  //     const T &b,
  //     locationt from,
  //     locationt to,
  //     const ai_cs_stackt &stack);
  //
  // This computes the join between "this" and "b".
  // Return true if "this" has changed.
};

// empty domain for testing purposes
class ai_cs_domain_empty:public ai_cs_domain_baset
{
public:
  virtual void transform(
    locationt from,
    locationt to,
    const ai_cs_stackt &stack,
    ai_cs_baset &ai,
    const namespacet &ns)
  {
  }

  bool merge(
    const ai_cs_domain_empty &b,
    locationt from,
    locationt to,
    const ai_cs_stackt &stack)
  {
    return false;
  }
};

// don't use me -- I am just a base class
// use ai_cst instead
class ai_cs_baset : public show_analysist
{
public:
  typedef goto_functionst::goto_functiont goto_functiont;
  typedef goto_programt::const_targett locationt;
  typedef ai_cs_domain_baset statet;
  
  // thread id is just a stack with topmost element being a thread create (or
  // the empty stack)
  typedef ai_cs_stackt thread_idt;

  typedef std::pair<ai_cs_stackt, locationt> placet;
  typedef std::set<placet> placest;

  // Maps identifiers of type "void *(*)(void *)" to function identifiers
  typedef std::map<irep_idt, irep_idt> fp_mapt;
  
  // create stack numbering
  ai_cs_baset(
   in_loopt &in_loop,
   bool handle_thread_exit=false) :
     ai_cs_baset(
       in_loop,
       *(new stack_numberingt()),
       handle_thread_exit,
       true) {}

  // reuse stack numbering
  ai_cs_baset(
   in_loopt &in_loop,
   stack_numberingt &stack_numbering,
   bool handle_thread_exit=false) :
     ai_cs_baset(
       in_loop,
       stack_numbering,
       handle_thread_exit,
       false) {}

  // reuse trie stack numbering
  ai_cs_baset(
   in_loopt &in_loop,
   trie_stack_numberingt &trie_stack_numbering,
   bool handle_thread_exit=false) :
     ai_cs_baset(
       in_loop,
       trie_stack_numbering,
       handle_thread_exit,
       false) {}

private:
  // for delegation
  ai_cs_baset(
    in_loopt &in_loop,
    stack_numberingt &stack_numbering,
    bool handle_thread_exit,
    bool destroy_stack_numbering) :
      in_loop(in_loop), all_in_slice(true),
      handle_thread_exit(handle_thread_exit),
      use_trie(false),
      stack_numbering(stack_numbering),
      destroy_stack_numbering(destroy_stack_numbering),
      trie_stack_numbering(*(new trie_stack_numberingt())),
      destroy_trie_stack_numbering(true),
      used(false),
      num_thread_create(0), num_resolved_direct(0), num_resolved_fp(0),
      has_recursion(false)
  {
  }

  // for delegation
  ai_cs_baset(
    in_loopt &in_loop,
    trie_stack_numberingt &trie_stack_numbering,
    bool handle_thread_exit,
    bool destroy_trie_stack_numbering) :
      in_loop(in_loop), all_in_slice(true),
      handle_thread_exit(handle_thread_exit),
      use_trie(true),
      stack_numbering(*(new stack_numberingt())),
      destroy_stack_numbering(true),
      trie_stack_numbering(trie_stack_numbering),
      destroy_trie_stack_numbering(destroy_trie_stack_numbering),
      used(false),
      num_thread_create(0), num_resolved_direct(0), num_resolved_fp(0),
      has_recursion(false)
  {
  }

public:

  virtual ~ai_cs_baset()
  {
    if(destroy_stack_numbering)
      delete &stack_numbering;

    if(destroy_trie_stack_numbering)
      delete &trie_stack_numbering;
  }

  inline void operator()(
    const goto_programt &goto_program,
    const namespacet &ns)
  {
    assert(!used);
    used=true;

    goto_functionst goto_functions;
    initialize(goto_program, ns);
    entry_state(goto_program);
    fixedpoint(goto_program, goto_functions, ai_cs_stackt(), ns);
    postprocessing();
  }
    
  inline void operator()(
    const goto_functionst &goto_functions,
    const namespacet &ns)
  {
    assert(!used);
    used=true;

    initialize(goto_functions, ns);
    entry_state(goto_functions);
    fixedpoint(goto_functions, ns);
    postprocessing();
  }

  inline void operator()(
    const goto_functiont &goto_function,
    const namespacet &ns)
  {
    assert(!used);
    used=true;

    goto_functionst goto_functions;
    initialize(goto_function, ns);
    entry_state(goto_function.body);
    fixedpoint(goto_function.body, goto_functions, ai_cs_stackt(), ns);
    postprocessing();
  }

  virtual void clear()
  {
    stack_numbering.clear();
  }

  // output per function, context, and location
  virtual void output(
    const namespacet &ns,
    const goto_functionst &goto_functions,
    std::ostream &out) const;

  // output per context and location
  virtual void output(
    const namespacet &ns,
    const goto_programt &goto_program,
    std::ostream &out) const;

  // output per context and location
  virtual void output(
    const namespacet &ns,
    const goto_functiont &goto_function,
    std::ostream &out) const
  {
    assert(goto_function.body_available());
    output(ns, goto_function.body, out);
  }

  virtual void output_stats(std::ostream &out)
  {
    assert(used);

    compute_stats(); // compute additional stats

    assert(max_length_place);
    assert(avg_length_place);

    out << "*** Statistics: " << "\n";
    out << "  Thread creates: " << num_thread_create << "\n";
    out << "  Thread creates resolved direct: " << num_resolved_direct
      << "\n";
    out << "  Thread creates resolved fp: " << num_resolved_fp << "\n";
    out << "  Number of places: " << num_places() << "\n";
    out << "  Number of stacks: " << num_stacks() << "\n";
    out << "  Maximum length of a place: " << max_length_place << "\n";
    out << "  Average length of a place: " << avg_length_place << "\n";
    out << "  Has recursion: " << (has_recursion ? "true" : "false");
  }

  unsigned get_stack_number(const ai_cs_stackt &stack)
  {
    if(use_trie)
      return trie_stack_numbering(stack.frames);
    else
      return stack_numbering(stack);
  }

  unsigned get_stack_number(const ai_cs_stackt &stack) const
  {
    unsigned stack_number;
    bool b;
    if(use_trie)
      b=trie_stack_numbering.get_number(stack.frames, stack_number);
    else
      b=stack_numbering.get_number(stack, stack_number);
    assert(!b);
    return stack_number;
  }

  const ai_cs_stackt &get_stack(unsigned n) const
  {
    assert(!use_trie);
    return stack_numbering.get_object(n);
  }

  const ai_cs_stackt get_stack_trie(unsigned n) const
  {
    assert(use_trie);
    ai_cs_stackt stack;
    trie_stack_numbering.get_object(n, stack.frames);
    return stack;
  }

  // get thread id
  thread_idt get_thread_id(const ai_cs_stackt &stack)
  {
    thread_idt thread_id=stack;
    thread_id.remove_top_calls();
    return thread_id;
  }

  // check if thread id is valid
  bool is_thread_id(const thread_idt &thread_id)
  {
    return !thread_id.has_top_calls();
  }

  // check if a statement is in a loop
  bool is_in_loop(locationt loc)
  {
    return in_loop.is_in_loop(loc);
  }

  // check if a statement is in a loop (transitively over function
  // calls and thread creation)
  bool is_in_loop(const ai_cs_stackt &stack, locationt loc)
  {
    if (is_in_loop(loc))
      return true;

    for (ai_cs_stackt::framest::const_iterator it=stack.frames.begin();
         it!=stack.frames.end(); it++)
    {
      if (is_in_loop(std::get<1>(*it)))
        return true;
    }

    return false;
  }

  std::set<locationt> &get_slice()
  {
    all_in_slice=false;
    return slice;
  }

protected:
  in_loopt &in_loop;

  bool all_in_slice;
  std::set<locationt> slice;

  bool handle_thread_exit;

  bool use_trie;

  stack_numberingt &stack_numbering;
  const bool destroy_stack_numbering;

  trie_stack_numberingt &trie_stack_numbering;
  const bool destroy_trie_stack_numbering;

  bool used;

  // stats about created thread resolution
  unsigned num_thread_create; // number of times create was encountered
  unsigned num_resolved_direct; // resolved directly
  unsigned num_resolved_fp; // resolved via function pointer

  unsigned max_length_place;
  unsigned avg_length_place;

  virtual void postprocessing()
  {
  }

  // flow-insensitive, context- and thread-sensitive function pointer
  // state
  typedef std::map<ai_cs_stackt, fp_mapt> fp_state_mapt;
  fp_state_mapt fp_state_map;

  // test if expression is of function pointer type
  bool is_function_pointer(const exprt &expr)
  {
    const typet &type=expr.type();
    return type.id()==ID_pointer && type.subtype().id()==ID_code;
  }

  bool is_create_thread(locationt l)
  {
    if (l->is_function_call())
    {
      const irep_idt identifier=misc::get_function_name(l);
      if(!identifier.empty())
      {
        if(id2string(identifier)==config.ansi_c.create_thread)
        {
          return true;
        }
      }
    }
    return false;
  }

  // find identifier of function referred to by expr
  std::pair<bool, const irep_idt> get_function_identifier(
    const ai_cs_stackt &stack,
    const exprt &expr,
    const goto_functionst &goto_functions);

  const goto_functiont &get_goto_function(
    const irep_idt &identifier,
    const goto_functionst &goto_functions)
  {
    goto_functionst::function_mapt::const_iterator it;
    it=goto_functions.function_map.find(identifier);
    assert(it!=goto_functions.function_map.end());
    return it->second;
  }

  // add mapping for one argument-parameter pair
  void add_function_pointer_mapping(
    const ai_cs_stackt &old_stack,
    const ai_cs_stackt &new_stack,
    unsigned caller_arg_idx,
    unsigned callee_par_idx,
    const exprt::operandst &arguments, // arguments of call
    const goto_functiont &goto_function, // called function
    const goto_functionst &goto_functions);

  // add mappings for all argument-parameter pairs
  void update_function_pointer_mappings(
    const ai_cs_stackt &old_stack,
    const ai_cs_stackt &new_stack,
    const exprt::operandst &arguments,
    const goto_functiont &goto_function,
    const goto_functionst &goto_functions);

  virtual void initialize(
    const goto_programt &goto_program,
    const namespacet &ns);

  virtual void initialize(
    const goto_functiont &goto_function,
    const namespacet &ns);

  virtual void initialize(
    const goto_functionst &goto_functions,
    const namespacet &ns);

  // entry state of the program
  void entry_state(const goto_programt &goto_program);
  void entry_state(const goto_functionst &goto_functions);

  // output the state per location, invokes output function of the
  // domain element
  virtual void output(
    const namespacet &ns,
    const goto_programt &goto_program,
    const irep_idt &identifier,
    const ai_cs_stackt &stack,
    std::ostream &out) const;

  typedef std::queue<placet> working_sett;

  placet get_next(working_sett &working_set);
  
  void put_in_working_set(
    working_sett &working_set,
    locationt l,
    const ai_cs_stackt &stack)
  {
    working_set.push(placet(stack, l));
  }

  virtual void fixedpoint(
    const goto_functionst &goto_functions,
    const namespacet &ns);

  // true = found s.th. new
  virtual bool fixedpoint(
    const goto_programt &goto_program,
    const goto_functionst &goto_functions,
    const ai_cs_stackt &stack,
    const namespacet &ns);

  // true = found s.th. new
  bool visit(
    locationt l,
    const ai_cs_stackt &stack,
    working_sett &working_set,
    const goto_programt &goto_program,
    const goto_functionst &goto_functions,
    const namespacet &ns);
  
  typedef std::set<irep_idt> recursion_sett;
  recursion_sett recursion_set;
  bool has_recursion;

  typedef std::map<ai_cs_stackt, std::set<locationt>> seen_mapt;
  seen_mapt seen_map;

  bool seen(const ai_cs_stackt &stack, locationt l)
  {
    seen_mapt::const_iterator it=seen_map.find(stack);
    if (it==seen_map.end())
      return false;

    const std::set<locationt> &seen_set=seen_map.at(stack);
    std::set<locationt>::const_iterator l_it=seen_set.find(l);
    if (l_it==seen_set.end())
      return false;

    return true;
  }

  void set_seen(const ai_cs_stackt &stack, locationt l)
  {
    seen_map[stack].insert(l);
  }

  // function calls
  // handles function pointer case distinctions and recursion
  bool do_function_call_rec(
    locationt l_call,
    locationt l_return,
    const ai_cs_stackt &stack,
    const exprt &function,
    const exprt::operandst &arguments,
    const goto_functionst &goto_functions,
    const namespacet &ns);

  void do_thread_create(
    locationt l_call,
    locationt l_return,
    const ai_cs_stackt &stack, // stack before this call
    const goto_functionst &goto_functions,
    const exprt::operandst &arguments, // function call arguments
    const namespacet &ns);

  bool do_function_call(
    locationt l_call,
    locationt l_return,
    const ai_cs_stackt &stack,
    const goto_functionst &goto_functions,
    const irep_idt &identifier,
    const exprt::operandst &arguments,
    const namespacet &ns);

  bool in_slice(locationt l) 
  { 
    if(all_in_slice)
      return true; 

    return slice.find(l) != slice.end();
  }

  // abstract methods

  virtual size_t num_places() const=0;

  virtual size_t num_stacks() const=0;

  virtual void compute_stats()=0;

  virtual bool merge(
    const statet &src,
    locationt from,
    locationt to,
    const ai_cs_stackt &stack)=0;

  virtual statet* make_temporary_state(const statet &s)=0;

  virtual statet &get_state(const ai_cs_stackt &stack, locationt l)=0;

  virtual const statet &get_const_state(
    const ai_cs_stackt &stack,
    locationt l)=0;

  virtual bool has(const placet &place) const=0;

  virtual const statet &find_state(
    const ai_cs_stackt &stack,
    locationt l) const=0;

  virtual void find_stacks(
    locationt l,
    std::set<ai_cs_stackt> &stacks) const=0;
};

std::ostream &operator<<(std::ostream &out, const ai_cs_baset::fp_mapt &fp_map);
std::ostream &operator<<(std::ostream &out, const ai_cs_baset::placet &place);
std::ostream &operator<<(std::ostream &out, const ai_cs_baset::placest &places);

// domainT is expected to be derived from ai_cs_domain_baseT
// this class contains the code that has to use the concrete class domainT
template<typename domainT>
class ai_cst:public ai_cs_baset
{
public:
  // flow-, context-, and thread-sensitive state
  typedef std::map<locationt, domainT> location_mapt;
  typedef std::map<unsigned, location_mapt> state_mapt;

  // constructor
  ai_cst(in_loopt &in_loop, bool handle_thread_exit=false):
    ai_cs_baset(in_loop, handle_thread_exit)
  {
  }

  ai_cst(
    in_loopt &in_loop,
    stack_numberingt &stack_numbering,
    bool handle_thread_exit=false):
    ai_cs_baset(in_loop, stack_numbering, handle_thread_exit)
  {
  }

  ai_cst(
    in_loopt &in_loop,
    trie_stack_numberingt &trie_stack_numbering,
    bool handle_thread_exit=false):
    ai_cs_baset(in_loop, trie_stack_numbering, handle_thread_exit)
  {
  }

  virtual const domainT &operator[](const placet &place) const
  {
    unsigned sn=get_stack_number(place.first);

    typename state_mapt::const_iterator it1=state_map.find(sn);
    chk(it1!=state_map.end(), "failed to find stack");

    const location_mapt &lm=it1->second;
    typename location_mapt::const_iterator it2=lm.find(place.second);
    chk(it2!=lm.end(), "failed to find location");

    return it2->second;
  }
  
  virtual bool has(const placet &place) const
  {
    unsigned sn=get_stack_number(place.first);

    typename state_mapt::const_iterator it1=state_map.find(sn);
    if(it1==state_map.end())
      return false;

    const location_mapt &lm=it1->second;
    typename location_mapt::const_iterator it2=lm.find(place.second);
    return it2!=lm.end();
  }

  virtual void clear()
  {
    state_map.clear();
    ai_cs_baset::clear();
  }

  virtual size_t num_places() const
  {
    size_t sum=0;

    for(typename state_mapt::const_iterator it=state_map.begin();
        it!=state_map.end(); it++)
    {
      const location_mapt &lm=it->second;
      sum+=lm.size();
    }

    return sum;
  }

  virtual size_t num_stacks() const
  {
    return state_map.size();
  }

  virtual const state_mapt &get_state_map()
  {
    return state_map;
  }

protected:
  state_mapt state_map;

  // this one creates states, if need be
  virtual statet &get_state(const ai_cs_stackt &stack, locationt l)
  {
    unsigned sn=get_stack_number(stack);
    location_mapt &lm=state_map[sn]; // calls default constructor
    return lm[l]; // calls default constructor
  }

  virtual const statet &get_const_state(const ai_cs_stackt &stack, locationt l)
  {
    unsigned sn=get_stack_number(stack);
    location_mapt &lm=state_map[sn]; // calls default constructor
    return lm[l]; // calls default constructor
  }

  // this one just finds states
  virtual const statet &find_state(
    const ai_cs_stackt &stack,
    locationt l) const
  {
    unsigned sn=get_stack_number(stack);

    typename state_mapt::const_iterator it1=state_map.find(sn);
    chk(it1!=state_map.end(), "failed to find stack");

    const location_mapt &lm=it1->second;
    typename location_mapt::const_iterator it2=lm.find(l);
    chk(it2!=lm.end(), "failed to find location");

    return it2->second;
  }

  // find all contexts for which we have information for the given
  // location (use for printing output only)
  virtual void find_stacks(locationt l, std::set<ai_cs_stackt> &stacks) const
  {
    for(typename state_mapt::const_iterator it1=state_map.begin();
        it1!=state_map.end(); it1++)
    {
      const location_mapt &lm=it1->second;

      for(typename location_mapt::const_iterator it2=lm.begin();
          it2!=lm.end(); it2++)
      {
        if(it2->first==l)
          stacks.insert(stack_numbering.get_object(it1->first));
      }
    }
  }

  virtual void compute_stats()
  {
    max_length_place=0;
    avg_length_place=0;

    unsigned num=0;
    unsigned total=0;

    for(typename state_mapt::const_iterator it1=state_map.begin();
        it1!=state_map.end(); it1++)
    {
      unsigned sn=it1->first;

      size_t sz=0;
      if(use_trie)
      {
        ai_cs_stackt stack;
        stack=get_stack_trie(sn);
        sz=stack.frames.size();
      }
      else
      {
        const ai_cs_stackt &stack=get_stack(sn);
        sz=stack.frames.size();
      }

      if(sz+1>max_length_place)
        max_length_place=sz+1;

      size_t num_locs=it1->second.size();
      total+=(sz+1)*num_locs;
      num+=num_locs;
    }

    avg_length_place=total/num;
  }

  virtual bool merge(
    const statet &src,
    locationt from,
    locationt to,
    const ai_cs_stackt &stack)
  {
    statet &dest=get_state(stack, to);
    return static_cast<domainT &>(dest).merge(
      static_cast<const domainT &>(src), from, to, stack);
  }

  virtual statet *make_temporary_state(const statet &s)
  {
    return new domainT(static_cast<const domainT &>(s));
  }

private:  
  // to enforce that domainT is derived from ai_cs_domain_baset
  void dummy(const domainT &s) { const statet &x=s; (void)x; }
};

template<
  typename domainT,
  typename DomainHash,
  typename DomainEqual=std::equal_to<domainT>
>
class ai_one_cst:public ai_cst<domainT>
{
public:
  typedef ai_cst<domainT> baset;
  typedef typename baset::placet placet;
  typedef typename baset::state_mapt state_mapt;
  typedef typename baset::statet statet;
  typedef typename baset::locationt locationt;

  using baset::state_map;

  // flow-, context-, and thread-sensitive state
  typedef map_one_cont<placet, domainT, DomainHash, DomainEqual> state_map_onet;

  //typedef map_one_cont<placet, domainT, DomainHash, DomainEqual,
  //  std::less<placet>, true> state_map_onet;

  // constructor
  ai_one_cst(in_loopt &in_loop, bool handle_thread_exit=false):
    ai_cst<domainT>(in_loop, handle_thread_exit)
  {
  }

  virtual const domainT &operator[](const placet &place) const
  {
    typename state_map_onet::const_iterator it=state_map_one.find(place);
    chk(it!=state_map_one.end(), "failed to find state");
    return (*it).second; // no ->
  }

  virtual bool has(const placet &place) const
  {
    typename state_map_onet::const_iterator it=state_map_one.find(place);
    return it!=state_map_one.end();
  }

  virtual void clear()
  {
    state_map_one.clear();
    baset::clear();
  }

  virtual size_t num_places() const
  {
    return state_map_one.size();
  }

  virtual size_t num_stacks() const
  {
    assert(false);
    return 0;
  }

  virtual const state_mapt &get_state_map()
  {
    assert(false);
    return state_map;
  }

  virtual const state_map_onet &get_state_map_one()
  {
    return state_map_one;
  }

protected:
  state_map_onet state_map_one;

  // this one creates states, if need be
  virtual statet &get_state(const ai_cs_stackt &stack, locationt l)
  {
    const placet place(stack, l);
    return state_map_one[place]; // calls default constructor
  }

  virtual const statet &get_const_state(const ai_cs_stackt &stack, locationt l)
  {
    const placet place(stack, l);
    return state_map_one.create_and_value_at(place);
  }

  // this one just finds states
  virtual const statet &find_state(
    const ai_cs_stackt &stack,
    locationt l) const
  {
    const placet place(stack, l);

    typename state_map_onet::const_iterator it=state_map_one.find(place);
    chk(it!=state_map_one.end(), "failed to find state");
    return (*it).second; // no ->
  }

  // find all contexts for which we have information for the given
  // location (use for printing output only)
  virtual void find_stacks(locationt l, std::set<ai_cs_stackt> &stacks) const
  {
    for(typename state_map_onet::const_iterator it=state_map_one.begin();
        it!=state_map_one.end(); it++)
    {
      const placet &place=(*it).first; // no ->
      if(place.second==l)
        stacks.insert(place.first);
    }
  }

  virtual void compute_stats()
  {
    assert(false);
  }
};

#endif
