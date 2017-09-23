/*******************************************************************\

Module: Flow Insensitive Static Analysis

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

/// \file
/// Flow Insensitive Static Analysis

#ifndef CPROVER_ANALYSES_FLOW_INSENSITIVE_ANALYSIS_H
#define CPROVER_ANALYSES_FLOW_INSENSITIVE_ANALYSIS_H

#include <queue>
#include <map>
#include <iosfwd>
#include <unordered_set>

#include <goto-programs/goto_functions.h>

// don't use me -- I am just a base class
// please derive from me
class flow_insensitive_abstract_domain_baset
{
public:
  flow_insensitive_abstract_domain_baset():
    changed(false)
  {
  }

  using locationt = goto_programt::const_targett;

  virtual void initialize(const namespacet &ns)=0;

  virtual bool transform(
    const namespacet &ns,
    locationt from,
    locationt to)=0;

  virtual ~flow_insensitive_abstract_domain_baset()
  {
  }

  virtual void output(
    const namespacet &ns,
    std::ostream &out) const
  {
  }

  using expr_sett = std::unordered_set<exprt, irep_hash>;

  virtual void get_reference_set(
    const namespacet &ns,
    const exprt &expr,
    expr_sett &expr_set)
  {
    // dummy, overload me!
    expr_set.clear();
  }

  virtual void clear(void)=0;

protected:
  bool changed;
  // utilities

  // get guard of a conditional edge
  exprt get_guard(locationt from, locationt to) const;

  // get lhs that return value is assigned to
  // for an edge that returns from a function
  exprt get_return_lhs(locationt to) const;
};

class flow_insensitive_analysis_baset
{
public:
  using statet = flow_insensitive_abstract_domain_baset;
  using locationt = goto_programt::const_targett;

  std::set<locationt> seen_locations;

  std::map<locationt, unsigned> statistics;

  bool seen(const locationt &l)
  {
    return (seen_locations.find(l)!=seen_locations.end());
  }

  explicit flow_insensitive_analysis_baset(const namespacet &_ns):
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
    }
  }

  virtual void initialize(
    const goto_functionst &goto_functions)
  {
    if(!initialized)
    {
      initialized=true;
    }
  }

  virtual void update(const goto_programt &goto_program);

  virtual void update(const goto_functionst &goto_functions);

  virtual void operator()(
    const goto_programt &goto_program);

  virtual void operator()(
    const goto_functionst &goto_functions);

  virtual ~flow_insensitive_analysis_baset()
  {
  }

  virtual void clear()
  {
    initialized=false;
  }

  virtual void output(
    const goto_functionst &goto_functions,
    std::ostream &out);

  virtual void output(
    const goto_programt &goto_program,
    std::ostream &out)
  {
    output(goto_program, "", out);
  }

protected:
  const namespacet &ns;

  virtual void output(
    const goto_programt &goto_program,
    const irep_idt &identifier,
    std::ostream &out) const;

  using working_sett = std::priority_queue<locationt>;

  locationt get_next(working_sett &working_set);

  void put_in_working_set(
    working_sett &working_set,
    locationt l)
  {
    working_set.push(l);
  }

  // true = found something new
  bool fixedpoint(
    const goto_programt &goto_program,
    const goto_functionst &goto_functions);

  bool fixedpoint(
    goto_functionst::function_mapt::const_iterator it,
    const goto_functionst &goto_functions);

  void fixedpoint(
    const goto_functionst &goto_functions);

  // true = found something new
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

  using functions_donet = std::set<irep_idt>;
  functions_donet functions_done;

  using recursion_sett = std::set<irep_idt>;
  recursion_sett recursion_set;

  bool initialized;

  // function calls
  bool do_function_call_rec(
    locationt l_call,
    const exprt &function,
    const exprt::operandst &arguments,
    statet &new_state,
    const goto_functionst &goto_functions);

  bool do_function_call(
    locationt l_call,
    const goto_functionst &goto_functions,
    const goto_functionst::function_mapt::const_iterator f_it,
    const exprt::operandst &arguments,
    statet &new_state);

  // abstract methods

  virtual statet &get_state()=0;
  virtual const statet &get_state() const=0;

  using expr_sett = flow_insensitive_abstract_domain_baset::expr_sett;

  virtual void get_reference_set(
    const exprt &expr,
    expr_sett &expr_set)=0;
};


template<typename T>
class flow_insensitive_analysist:public flow_insensitive_analysis_baset
{
public:
  // constructor
  explicit flow_insensitive_analysist(const namespacet &_ns):
    flow_insensitive_analysis_baset(_ns)
  {
  }

  using locationt = goto_programt::const_targett;

  virtual void clear()
  {
    state.clear();
    flow_insensitive_analysis_baset::clear();
  }

  T &get_data() { return state; }
  const T &get_data() const { return state; }

protected:
  T state; // one global state

  virtual statet &get_state() { return state; }

  virtual const statet &get_state() const { return state; }

  void get_reference_set(
    const exprt &expr,
    expr_sett &expr_set)
  {
    state.get_reference_set(ns, expr, expr_set);
  }

private:
  // to enforce that T is derived from abstract_domain_baset
  void dummy(const T &s) { const statet &x=dummy1(s); (void)x; }
};

#endif // CPROVER_ANALYSES_FLOW_INSENSITIVE_ANALYSIS_H
