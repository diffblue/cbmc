/*******************************************************************\

Module: Abstract Interpretation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANALYSES_AI_H
#define CPROVER_ANALYSES_AI_H

#include <map>
#include <iosfwd>

#include <goto-programs/goto_functions.h>

// forward reference
class ai_baset;

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
  
  // how function calls are treated:
  // a) there is an edge from each call site to the function head
  // b) there is an edge from each return to the last instruction (END_FUNCTION)
  //    of each function
  // c) there is an edge from the last instruction of the function
  //    to the instruction following the call site
  //    (for setting the LHS)

  virtual void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns)=0;

  virtual void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const
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

  ai_baset()
  {
  }
  
  virtual ~ai_baset()
  {
  }

  inline void operator()(
    const goto_programt &goto_program,
    const namespacet &ns)
  {
    goto_functionst goto_functions;
    initialize(goto_program);
    fixedpoint(goto_program, goto_functions, ns);
  }
    
  inline void operator()(
    const goto_functionst &goto_functions,
    const namespacet &ns)
  {
    initialize(goto_functions);
    fixedpoint(goto_functions, ns);
  }

  inline void operator()(
    const goto_functionst::goto_functiont &goto_function,
    const namespacet &ns)
  {
    goto_functionst goto_functions;
    initialize(goto_function);
    fixedpoint(goto_function.body, goto_functions, ns);
  }

  virtual void clear()
  {
  }
  
  virtual void output(
    const namespacet &ns,
    const goto_functionst &goto_functions,
    std::ostream &out) const;

  inline void output(
    const namespacet &ns,
    const goto_programt &goto_program,
    std::ostream &out) const
  {
    output(ns, goto_program, "", out);
  }

  inline void output(
    const namespacet &ns,
    const goto_functionst::goto_functiont &goto_function,
    std::ostream &out) const
  {
    output(ns, goto_function.body, "", out);
  }

protected:
  // overload to add a factory
  virtual void initialize(const goto_programt &);
  virtual void initialize(const goto_functionst::goto_functiont &);
  virtual void initialize(const goto_functionst &);

  virtual void output(
    const namespacet &ns,
    const goto_programt &goto_program,
    const irep_idt &identifier,
    std::ostream &out) const;

  // the work-queue is sorted by location number
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
    const goto_functionst &goto_functions,
    const namespacet &ns);
    
  void fixedpoint(
    const goto_functionst &goto_functions,
    const namespacet &ns);

  // true = found s.th. new
  bool visit(
    locationt l,
    working_sett &working_set,
    const goto_programt &goto_program,
    const goto_functionst &goto_functions,
    const namespacet &ns);
    
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
    const goto_functionst &goto_functions,
    const namespacet &ns);

  bool do_function_call(
    locationt l_call, locationt l_return,
    const goto_functionst &goto_functions,
    const goto_functionst::function_mapt::const_iterator f_it,
    const exprt::operandst &arguments,
    const namespacet &ns);

  // abstract methods
    
  virtual bool merge(const statet &src, locationt from, locationt to)=0;
  virtual statet &get_state(locationt l)=0;
  virtual const statet &find_state(locationt l) const=0;
  virtual statet* make_temporary_state(const statet &s)=0;
};

// domainT is expected to be derived from ai_domain_baseT
template<typename domainT>
class ait:public ai_baset
{
public:
  // constructor
  ait():ai_baset()
  {
  }

  typedef goto_programt::const_targett locationt;

  inline domainT &operator[](locationt l)
  {
    typename state_mapt::iterator it=state_map.find(l);
    if(it==state_map.end()) throw "failed to find state";
    return it->second;
  }
    
  inline const domainT &operator[](locationt l) const
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
  typedef std::map<locationt, domainT> state_mapt;
  state_mapt state_map;

  // this one creates states, if need be
  virtual statet &get_state(locationt l)
  {
    return state_map[l]; // calls default constructor
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
    return static_cast<domainT &>(dest).merge(static_cast<const domainT &>(src), from, to);
  }
  
  virtual statet *make_temporary_state(const statet &s)
  {
    return new domainT(static_cast<const domainT &>(s));
  }

private:  
  // to enforce that domainT is derived from ai_domain_baset
  void dummy(const domainT &s) { const statet &x=s; (void)x; }
};

#endif
