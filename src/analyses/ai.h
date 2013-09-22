/*******************************************************************\

Module: Abstract Interpretation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANALYSES_AI_H
#define CPROVER_ANALYSES_AI_H

#include <map>
#include <ostream>

#include <goto-programs/goto_functions.h>

// don't use me -- I am just a base class
// please derive from me
class ai_domain_baset
{
public:
  // The constructor is expected to produce 'false'
  // or 'bottom'
  ai_domain_baset()
  {
  }

  virtual ~ai_domain_baset()
  {
  }
  
  typedef goto_programt::const_targett locationt;
  
  // produce initial state
  virtual void make_entry_state()
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

  virtual void output(
    const namespacet &ns,
    std::ostream &out) const
  {
  }
  
  // also add
  //
  //   bool merge(const T &b, locationt from, locationt to);
  //
  // This computes the join between "this" and "b".
  // Return true if "this" has changed.
};

// don't use me -- I am just a base class
// use ait instead
class ai_baset
{
public:
  typedef ai_domain_baset statet;
  typedef goto_programt::const_targett locationt;

  explicit ai_baset(const namespacet &_ns):ns(_ns)
  {
  }
  
  virtual ~ai_baset()
  {
  }

  inline void operator()(
    const goto_programt &goto_program)
  {
    goto_functionst goto_functions;
    initialize(goto_program);
    entry_point(goto_program);
    fixedpoint(goto_program, goto_functions);
  }
    
  inline void operator()(
    const goto_functionst &goto_functions)
  {
    initialize(goto_functions);
    entry_point(goto_functions);
    fixedpoint(goto_functions);      
  }

  virtual void clear()
  {
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
  
  void initialize(const goto_programt &);
  void initialize(const goto_functionst &);
  void entry_point(const goto_programt &);
  void entry_point(const goto_functionst &);

  // true = found s.th. new
  bool fixedpoint(
    const goto_programt &goto_program,
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
  
  typedef std::set<irep_idt> recursion_sett;
  recursion_sett recursion_set;
    
  // function calls
  bool do_function_call_rec(
    locationt l_call, locationt l_return,
    const exprt &function,
    const exprt::operandst &arguments,
    const goto_functionst &goto_functions);

  bool do_function_call(
    locationt l_call, locationt l_return,
    const goto_functionst &goto_functions,
    const goto_functionst::function_mapt::const_iterator f_it,
    const exprt::operandst &arguments);

  // abstract methods
    
  virtual bool merge(const statet &src, locationt from, locationt to)=0;
  virtual statet &get_state(locationt l)=0;
  virtual const statet &find_state(locationt l) const=0;
  virtual statet* make_temporary_state(const statet &s)=0;
};

// T is expected to be derived from domain_baset
template<typename T>
class ait:public ai_baset
{
public:
  // constructor
  explicit ait(const namespacet &_ns):
    ai_baset(_ns)
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
    ai_baset::clear();
  }
  
protected:
  typedef std::map<locationt, T> state_mapt;
  state_mapt state_map;

  // this one creates states
  virtual statet &get_state(locationt l)
  {
    return state_map[l]; // create if need be
  }

  // this one just finds states
  virtual const statet &find_state(locationt l) const
  {
    typename state_mapt::const_iterator it=state_map.find(l);
    if(it==state_map.end()) throw "failed to find state";
    return it->second;
  }

  virtual bool merge(const statet &src, locationt from, locationt to)
  {
    statet &dest=get_state(to);
    return static_cast<T &>(dest).merge(static_cast<const T &>(src), from, to);
  }
  
  virtual statet *make_temporary_state(const statet &s)
  {
    return new T(static_cast<const T &>(s));
  }

private:  
  // to enforce that T is derived from ai_domain_baset
  void dummy(const T &s) { const statet &x=s; }
};

#endif
