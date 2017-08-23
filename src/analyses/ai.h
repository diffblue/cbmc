/*******************************************************************\

Module: Abstract Interpretation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstract Interpretation

#ifndef CPROVER_ANALYSES_AI_H
#define CPROVER_ANALYSES_AI_H

#include <map>
#include <iosfwd>

#include <util/json.h>
#include <util/xml.h>
#include <util/expr.h>

#include <goto-programs/goto_model.h>

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
  // b) there is an edge from the last instruction (END_FUNCTION)
  //    of the function to the instruction _following_ the call site
  //    (this also needs to set the LHS, if applicable)

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

  virtual jsont output_json(
    const ai_baset &ai,
    const namespacet &ns) const;

  virtual xmlt output_xml(
    const ai_baset &ai,
    const namespacet &ns) const;

  // no states
  virtual void make_bottom()=0;

  // all states -- the analysis doesn't use this,
  // and domains may refuse to implement it.
  virtual void make_top()=0;

  // a reasonable entry-point state
  virtual void make_entry()=0;

  virtual bool is_bottom() const=0;

  virtual bool is_top() const=0;

  // also add
  //
  //   bool merge(const T &b, locationt from, locationt to);
  //
  // This computes the join between "this" and "b".
  // Return true if "this" has changed.

  // This method allows an expression to be simplified / evaluated using the
  // current state.  It is used to evaluate assertions and in program
  // simplification

  // return true if unchanged
  virtual bool ai_simplify(
    exprt &condition,
    const namespacet &ns) const
  {
    return true;
  }

  // Simplifies the expression but keeps it as an l-value
  virtual bool ai_simplify_lhs(
    exprt &condition,
    const namespacet &ns) const;

  // Applies the changes between the start and end to the domain
  virtual void merge_three_way_function_return(
    const ai_domain_baset &function_call,
    const ai_domain_baset &function_start,
    const ai_domain_baset &function_end,
    const namespacet &ns)
  {
    // Take the state at the end of the function as a over-approximation
    // of applying the changes in the function
  }

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

  void operator()(
    const goto_programt &goto_program,
    const namespacet &ns)
  {
    goto_functionst goto_functions;
    initialize(goto_program);
    entry_state(goto_program);
    fixedpoint(goto_program, goto_functions, ns);
  }

  void operator()(
    const goto_functionst &goto_functions,
    const namespacet &ns)
  {
    initialize(goto_functions);
    entry_state(goto_functions);
    fixedpoint(goto_functions, ns);
  }

  void operator()(const goto_modelt &goto_model)
  {
    const namespacet ns(goto_model.symbol_table);
    initialize(goto_model.goto_functions);
    entry_state(goto_model.goto_functions);
    fixedpoint(goto_model.goto_functions, ns);
  }

  void operator()(
    const goto_functionst::goto_functiont &goto_function,
    const namespacet &ns)
  {
    goto_functionst goto_functions;
    initialize(goto_function);
    entry_state(goto_function.body);
    fixedpoint(goto_function.body, goto_functions, ns);
  }

  virtual void clear()
  {
  }

  virtual void output(
    const namespacet &ns,
    const goto_functionst &goto_functions,
    std::ostream &out) const;

  void output(
    const goto_modelt &goto_model,
    std::ostream &out) const
  {
    const namespacet ns(goto_model.symbol_table);
    output(ns, goto_model.goto_functions, out);
  }

  void output(
    const namespacet &ns,
    const goto_programt &goto_program,
    std::ostream &out) const
  {
    output(ns, goto_program, "", out);
  }

  void output(
    const namespacet &ns,
    const goto_functionst::goto_functiont &goto_function,
    std::ostream &out) const
  {
    output(ns, goto_function.body, "", out);
  }


  virtual jsont output_json(
    const namespacet &ns,
    const goto_functionst &goto_functions) const;

  jsont output_json(
    const goto_modelt &goto_model) const
  {
    const namespacet ns(goto_model.symbol_table);
    return output_json(ns, goto_model.goto_functions);
  }

  jsont output_json(
    const namespacet &ns,
    const goto_programt &goto_program) const
  {
    return output_json(ns, goto_program, "");
  }

  jsont output_json(
    const namespacet &ns,
    const goto_functionst::goto_functiont &goto_function) const
  {
    return output_json(ns, goto_function.body, "");
  }


  virtual xmlt output_xml(
    const namespacet &ns,
    const goto_functionst &goto_functions) const;

  xmlt output_xml(
    const goto_modelt &goto_model) const
  {
    const namespacet ns(goto_model.symbol_table);
    return output_xml(ns, goto_model.goto_functions);
  }

  xmlt output_xml(
    const namespacet &ns,
    const goto_programt &goto_program) const
  {
    return output_xml(ns, goto_program, "");
  }

  xmlt output_xml(
    const namespacet &ns,
    const goto_functionst::goto_functiont &goto_function) const
  {
    return output_xml(ns, goto_function.body, "");
  }

protected:
  // overload to add a factory
  virtual void initialize(const goto_programt &);
  virtual void initialize(const goto_functionst::goto_functiont &);
  virtual void initialize(const goto_functionst &);

  void entry_state(const goto_programt &);
  void entry_state(const goto_functionst &);

  virtual void output(
    const namespacet &ns,
    const goto_programt &goto_program,
    const irep_idt &identifier,
    std::ostream &out) const;

  virtual jsont output_json(
    const namespacet &ns,
    const goto_programt &goto_program,
    const irep_idt &identifier) const;

  virtual xmlt output_xml(
    const namespacet &ns,
    const goto_programt &goto_program,
    const irep_idt &identifier) const;


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

  virtual void fixedpoint(
    const goto_functionst &goto_functions,
    const namespacet &ns)=0;

  void sequential_fixedpoint(
    const goto_functionst &goto_functions,
    const namespacet &ns);
  void concurrent_fixedpoint(
    const goto_functionst &goto_functions,
    const namespacet &ns);

  // true = found s.th. new
  bool visit(
    locationt l,
    working_sett &working_set,
    const goto_programt &goto_program,
    const goto_functionst &goto_functions,
    const namespacet &ns);

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

  // for concurrent fixedpoint
  virtual bool merge_shared(
    const statet &src,
    locationt from,
    locationt to,
    const namespacet &ns)=0;
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

  domainT &operator[](locationt l)
  {
    typename state_mapt::iterator it=state_map.find(l);
    if(it==state_map.end())
      throw "failed to find state";

    return it->second;
  }

  const domainT &operator[](locationt l) const
  {
    typename state_mapt::const_iterator it=state_map.find(l);
    if(it==state_map.end())
      throw "failed to find state";

    return it->second;
  }

  void clear() override
  {
    state_map.clear();
    ai_baset::clear();
  }

protected:
  typedef std::unordered_map<locationt, domainT, const_target_hash> state_mapt;
  state_mapt state_map;

  // this one creates states, if need be
  virtual statet &get_state(locationt l) override
  {
    return state_map[l]; // calls default constructor
  }

  // this one just finds states
  const statet &find_state(locationt l) const override
  {
    typename state_mapt::const_iterator it=state_map.find(l);
    if(it==state_map.end())
      throw "failed to find state";

    return it->second;
  }

  /// Takes a state \p src, gets another state from the \p to location
  /// source_state (param)
  /// dest_state (built from to)
  /// Merge the source state into the destination state
  ///

  ///
  /// \param src
  /// \param from
  /// \param to
  /// \return
  ///
  bool merge(const statet &src, locationt from, locationt to) override
  {
    statet &dest=get_state(to);
    return static_cast<domainT &>(dest).merge(
      static_cast<const domainT &>(src), from, to);
  }

  statet *make_temporary_state(const statet &s) override
  {
    return new domainT(static_cast<const domainT &>(s));
  }

  void fixedpoint(
    const goto_functionst &goto_functions,
    const namespacet &ns) override
  {
    sequential_fixedpoint(goto_functions, ns);
  }

private:
  // to enforce that domainT is derived from ai_domain_baset
  void dummy(const domainT &s) { const statet &x=s; (void)x; }

  // not implemented in sequential analyses
  bool merge_shared(
    const statet &src,
    goto_programt::const_targett from,
    goto_programt::const_targett to,
    const namespacet &ns) override
  {
    throw "not implemented";
  }
};

template<typename domainT>
class concurrency_aware_ait:public ait<domainT>
{
public:
  typedef typename ait<domainT>::statet statet;

  // constructor
  concurrency_aware_ait():ait<domainT>()
  {
  }

  bool merge_shared(
    const statet &src,
    goto_programt::const_targett from,
    goto_programt::const_targett to,
    const namespacet &ns) override
  {
    statet &dest=this->get_state(to);
    return static_cast<domainT &>(dest).merge_shared(
      static_cast<const domainT &>(src), from, to, ns);
  }

protected:
  void fixedpoint(
    const goto_functionst &goto_functions,
    const namespacet &ns) override
  {
    this->concurrent_fixedpoint(goto_functions, ns);
  }
};

#endif // CPROVER_ANALYSES_AI_H
