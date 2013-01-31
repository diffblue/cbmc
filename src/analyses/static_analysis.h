/*******************************************************************\

Module: Static Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_STATIC_ANALYSIS_H
#define CPROVER_GOTO_PROGRAMS_STATIC_ANALYSIS_H

#include <map>
#include <ostream>

#include <goto-programs/goto_functions.h>

// don't use me -- I am just a base class
// please derive from me
class domain_baset
{
public:
  domain_baset():seen(false)
  {
  }

  typedef goto_programt::const_targett locationt;

  // will go away
  virtual void initialize(
    const namespacet &ns,
    locationt l)
  {
  }

  // how function calls are treated:
  // a) there is an edge from each call site to the function head
  // b) there is an edge from each return to the last instruction (END_FUNCTION)
  //    of each function
  // c) there is an edge from the last instruction of the function
  //    to the instruction following the call site
  //    (for setting the LHS)

  virtual void transform(
    const namespacet &ns,
    locationt from,
    locationt to)=0;

  virtual ~domain_baset()
  {
  }
  
  virtual void output(
    const namespacet &ns,
    std::ostream &out) const
  {
  }
  
  typedef hash_set_cont<exprt, irep_hash> expr_sett;

  // will go away  
  virtual void get_reference_set(
    const namespacet &ns,
    const exprt &expr,
    std::list<exprt> &dest)
  {
    // dummy, overload me!
    dest.clear();
  }
  
  // also add
  //
  //   bool merge(const T &b);
  //
  // this computes the join between "this" and b
  // return true if "this" has changed
  
protected:
  bool seen;
  
  friend class static_analysis_baset;
};

// don't use me -- I am just a base class
// use static_analysist instead
class static_analysis_baset
{
public:
  typedef domain_baset statet;
  typedef goto_programt::const_targett locationt;

  static_analysis_baset(const namespacet &_ns):
    ns(_ns),
    initialized(false)
  {
  }
  
  virtual void initialize(
    const goto_programt &goto_program)
  {
    if(!initialized)
    {
      initialized=true;
      generate_states(goto_program);
    }
  }
    
  virtual void initialize(
    const goto_functionst &goto_functions)
  {
    if(!initialized)
    {
      initialized=true;
      generate_states(goto_functions);
    }
  }
    
  virtual void update(const goto_programt &goto_program);
  virtual void update(const goto_functionst &goto_functions);
    
  virtual void operator()(
    const goto_programt &goto_program);
    
  virtual void operator()(
    const goto_functionst &goto_functions);

  virtual ~static_analysis_baset()
  {
  }

  virtual void clear()
  {
    initialized=false;
  }
  
  virtual void output(
    const goto_functionst &goto_functions,
    std::ostream &out) const;

  void output(
    const goto_programt &goto_program,
    std::ostream &out) const
  {
    output(goto_program, "", out);
  }

  virtual bool has_location(locationt l) const=0;
  
  void insert(locationt l)
  {
    generate_state(l);
  }

  // utilities  
  
  // get guard of a conditional edge
  static exprt get_guard(locationt from, locationt to);
  
  // get lhs that return value is assigned to
  // for an edge that returns from a function
  static exprt get_return_lhs(locationt to);

protected:
  const namespacet &ns;
  
  virtual void output(
    const goto_programt &goto_program,
    const irep_idt &identifier,
    std::ostream &out) const;

  typedef std::map<unsigned, locationt> working_sett;
  
  locationt get_next(working_sett &working_set);
  
  void put_in_working_set(
    working_sett &working_set,
    locationt l)
  {
    working_set.insert(
      std::pair<unsigned, locationt>(l->location_number, l));
  }

  // true = found s.th. new
  bool fixedpoint(
    const goto_programt &goto_program,
    const goto_functionst &goto_functions);
    
  bool fixedpoint(
    goto_functionst::function_mapt::const_iterator it,
    const goto_functionst &goto_functions);
    
  void fixedpoint(
    const goto_functionst &goto_functions);

  // true = found s.th. new
  bool visit(
    locationt l,
    working_sett &working_set,
    const goto_programt &goto_program,
    const goto_functionst &goto_functions);
    
  static locationt successor(locationt l)
  {
    l++;
    return l;
  }
  
  virtual bool merge(statet &a, const statet &b)=0;
  
  typedef std::set<irep_idt> functions_donet;
  functions_donet functions_done;

  typedef std::set<irep_idt> recursion_sett;
  recursion_sett recursion_set;
  
  void generate_states(
    const goto_functionst &goto_functions);

  void generate_states(
    const goto_programt &goto_program);
    
  bool initialized;
  
  // function calls
  void do_function_call_rec(
    locationt l_call,
    const exprt &function,
    const exprt::operandst &arguments,
    statet &new_state,
    const goto_functionst &goto_functions);

  void do_function_call(
    locationt l_call,
    const goto_functionst &goto_functions,
    const goto_functionst::function_mapt::const_iterator f_it,
    const exprt::operandst &arguments,
    statet &new_state);

  // abstract methods
    
  virtual void generate_state(locationt l)=0;
  virtual statet &get_state(locationt l)=0;
  virtual const statet &get_state(locationt l) const=0;
  virtual statet* make_temporary_state(statet &s)=0;

  typedef domain_baset::expr_sett expr_sett;

  virtual void get_reference_set(
    locationt l,
    const exprt &expr,
    std::list<exprt> &dest)=0;
};

// T is expected to be derived from domain_baset
template<typename T>
class static_analysist:public static_analysis_baset
{
public:
  // constructor
  static_analysist(const namespacet &_ns):
    static_analysis_baset(_ns)
  {
  }

  typedef goto_programt::const_targett locationt;

  inline T &operator[](locationt l)
  {
    typename state_mapt::iterator it=state_map.find(l);
    if(it==state_map.end()) throw "failed to find state";
    return it->second;
  }
    
  inline const T &operator[](locationt l) const
  {
    typename state_mapt::const_iterator it=state_map.find(l);
    if(it==state_map.end()) throw "failed to find state";
    return it->second;
  }
  
  virtual void clear()
  {
    state_map.clear();
    static_analysis_baset::clear();
  }

  virtual bool has_location(locationt l) const
  {
    return state_map.count(l)!=0;
  }
  
protected:
  typedef std::map<locationt, T> state_mapt;
  state_mapt state_map;

  virtual statet &get_state(locationt l)
  {
    typename state_mapt::iterator it=state_map.find(l);
    if(it==state_map.end()) throw "failed to find state";
    return it->second;
  }

  virtual const statet &get_state(locationt l) const
  {
    typename state_mapt::const_iterator it=state_map.find(l);
    if(it==state_map.end()) throw "failed to find state";
    return it->second;
  }

  virtual bool merge(statet &a, const statet &b)
  {
    return static_cast<T &>(a).merge(static_cast<const T &>(b));
  }
  
  virtual statet *make_temporary_state(statet &s)
  {
    return new T(static_cast<T &>(s));
  }

  virtual void generate_state(locationt l)
  {
    state_map[l].initialize(ns, l);
  }

  virtual void get_reference_set(
    locationt l,
    const exprt &expr,
    std::list<exprt> &dest)
  {
    state_map[l].get_reference_set(ns, expr, dest);
  }

private:  
  // to enforce that T is derived from domain_baset
  void dummy(const T &s) { const statet &x=dummy1(s); }
};

#endif
