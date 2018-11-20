/*******************************************************************\

Module: Abstract Interpretation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstract Interpretation

#ifndef CPROVER_ANALYSES_AI_H
#define CPROVER_ANALYSES_AI_H

#include <iosfwd>
#include <map>
#include <memory>

#include <util/json.h>
#include <util/xml.h>
#include <util/expr.h>
#include <util/make_unique.h>

#include <goto-programs/goto_model.h>

#include "ai_domain.h"

/// The basic interface of an abstract interpreter. This should be enough
/// to create, run and query an abstract interpreter.
///
/// Note: this is just a base class. \ref ait should be used instead.
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

  /// Run abstract interpretation on a single function
  void operator()(
    const irep_idt &function_identifier,
    const goto_programt &goto_program,
    const namespacet &ns)
  {
    goto_functionst goto_functions;
    initialize(goto_program);
    entry_state(goto_program);
    fixedpoint(function_identifier, goto_program, goto_functions, ns);
    finalize();
  }

  /// Run abstract interpretation on a whole program
  void operator()(
    const goto_functionst &goto_functions,
    const namespacet &ns)
  {
    initialize(goto_functions);
    entry_state(goto_functions);
    fixedpoint(goto_functions, ns);
    finalize();
  }

  /// Run abstract interpretation on a whole program
  void operator()(const goto_modelt &goto_model)
  {
    const namespacet ns(goto_model.symbol_table);
    initialize(goto_model.goto_functions);
    entry_state(goto_model.goto_functions);
    fixedpoint(goto_model.goto_functions, ns);
    finalize();
  }

  /// Run abstract interpretation on a single function
  void operator()(
    const irep_idt &function_identifier,
    const goto_functionst::goto_functiont &goto_function,
    const namespacet &ns)
  {
    goto_functionst goto_functions;
    initialize(goto_function);
    entry_state(goto_function.body);
    fixedpoint(function_identifier, goto_function.body, goto_functions, ns);
    finalize();
  }

  /// Get a copy of the abstract state before the given instruction, without
  /// needing to know what kind of domain or history is used. Note: intended
  /// for users of the abstract interpreter; derived classes should
  /// use \ref get_state or \ref find_state to access the actual underlying
  /// state.
  /// PRECONDITION(l is dereferenceable)
  /// \param l: The location before which we want the abstract state
  /// \return The abstract state before `l`. We return a pointer to a copy as
  ///   the method should be const and there are some non-trivial cases
  ///   including merging abstract states, etc.
  virtual std::unique_ptr<statet> abstract_state_before(locationt l) const = 0;

  /// Get a copy of the abstract state after the given instruction, without
  /// needing to know what kind of domain or history is used. Note: intended
  /// for users of the abstract interpreter; derived classes should
  /// use \ref get_state or \ref find_state to access the actual underlying
  /// state.
  /// \param l: The location before which we want the abstract state
  /// \return The abstract state after `l`. We return a pointer to a copy as
  ///   the method should be const and there are some non-trivial cases
  ///   including merging abstract states, etc.
  virtual std::unique_ptr<statet> abstract_state_after(locationt l) const
  {
    /// PRECONDITION(l is dereferenceable && std::next(l) is dereferenceable)
    /// Check relies on a DATA_INVARIANT of goto_programs
    INVARIANT(!l->is_end_function(), "No state after the last instruction");
    return abstract_state_before(std::next(l));
  }

  /// Reset the abstract state
  virtual void clear()
  {
  }

  /// Output the abstract states for a whole program
  virtual void output(
    const namespacet &ns,
    const goto_functionst &goto_functions,
    std::ostream &out) const;

  /// Output the abstract states for a whole program
  void output(
    const goto_modelt &goto_model,
    std::ostream &out) const
  {
    const namespacet ns(goto_model.symbol_table);
    output(ns, goto_model.goto_functions, out);
  }

  /// Output the abstract states for a function
  void output(
    const namespacet &ns,
    const goto_programt &goto_program,
    std::ostream &out) const
  {
    output(ns, goto_program, "", out);
  }

  /// Output the abstract states for a function
  void output(
    const namespacet &ns,
    const goto_functionst::goto_functiont &goto_function,
    std::ostream &out) const
  {
    output(ns, goto_function.body, "", out);
  }

  /// Output the abstract states for the whole program as JSON
  virtual jsont output_json(
    const namespacet &ns,
    const goto_functionst &goto_functions) const;

  /// Output the abstract states for a whole program as JSON
  jsont output_json(
    const goto_modelt &goto_model) const
  {
    const namespacet ns(goto_model.symbol_table);
    return output_json(ns, goto_model.goto_functions);
  }

  /// Output the abstract states for a single function as JSON
  jsont output_json(
    const namespacet &ns,
    const goto_programt &goto_program) const
  {
    return output_json(ns, goto_program, "");
  }

  /// Output the abstract states for a single function as JSON
  jsont output_json(
    const namespacet &ns,
    const goto_functionst::goto_functiont &goto_function) const
  {
    return output_json(ns, goto_function.body, "");
  }

  /// Output the abstract states for the whole program as XML
  virtual xmlt output_xml(
    const namespacet &ns,
    const goto_functionst &goto_functions) const;

  /// Output the abstract states for the whole program as XML
  xmlt output_xml(
    const goto_modelt &goto_model) const
  {
    const namespacet ns(goto_model.symbol_table);
    return output_xml(ns, goto_model.goto_functions);
  }

  /// Output the abstract states for a single function as XML
  xmlt output_xml(
    const namespacet &ns,
    const goto_programt &goto_program) const
  {
    return output_xml(ns, goto_program, "");
  }

  /// Output the abstract states for a single function as XML
  xmlt output_xml(
    const namespacet &ns,
    const goto_functionst::goto_functiont &goto_function) const
  {
    return output_xml(ns, goto_function.body, "");
  }

protected:
  /// Initialize all the abstract states for a single function. Override this to
  /// do custom per-domain initialization.
  virtual void initialize(const goto_programt &goto_program);

  /// Initialize all the abstract states for a single function.
  virtual void initialize(const goto_functionst::goto_functiont &goto_function);

  /// Initialize all the abstract states for a whole program. Override this to
  /// do custom per-analysis initialization.
  virtual void initialize(const goto_functionst &goto_functions);

  /// Override this to add a cleanup or post-processing step after fixedpoint
  /// has run
  virtual void finalize();

  /// Set the abstract state of the entry location of a single function to the
  /// entry state required by the analysis
  void entry_state(const goto_programt &goto_program);

  /// Set the abstract state of the entry location of a whole program to the
  /// entry state required by the analysis
  void entry_state(const goto_functionst &goto_functions);

  /// Output the abstract states for a single function
  /// \param ns: The namespace
  /// \param goto_program: The goto program
  /// \param identifier: The identifier used to find a symbol to identify the
  ///   source language
  /// \param out: The ostream to direct output to
  virtual void output(
    const namespacet &ns,
    const goto_programt &goto_program,
    const irep_idt &identifier,
    std::ostream &out) const;

  /// Output the abstract states for a single function as JSON
  /// \param ns: The namespace
  /// \param goto_program: The goto program
  /// \param identifier: The identifier used to find a symbol to identify the
  ///   source language
  /// \return The JSON object
  virtual jsont output_json(
    const namespacet &ns,
    const goto_programt &goto_program,
    const irep_idt &identifier) const;

  /// Output the abstract states for a single function as XML
  /// \param ns: The namespace
  /// \param goto_program: The goto program
  /// \param identifier: The identifier used to find a symbol to identify the
  ///   source language
  /// \return The XML object
  virtual xmlt output_xml(
    const namespacet &ns,
    const goto_programt &goto_program,
    const irep_idt &identifier) const;

  /// The work queue, sorted by location number
  typedef std::map<unsigned, locationt> working_sett;

  /// Get the next location from the work queue
  locationt get_next(working_sett &working_set);

  void put_in_working_set(
    working_sett &working_set,
    locationt l)
  {
    working_set.insert(
      std::pair<unsigned, locationt>(l->location_number, l));
  }

  /// Run the fixedpoint algorithm until it reaches a fixed point
  /// \return True if we found something new
  bool fixedpoint(
    const irep_idt &function_identifier,
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

  /// Perform one step of abstract interpretation from location l
  /// Depending on the instruction type it may compute a number of "edges"
  /// or applications of the abstract transformer
  /// \return True if the state was changed
  bool visit(
    const irep_idt &function_identifier,
    locationt l,
    working_sett &working_set,
    const goto_programt &goto_program,
    const goto_functionst &goto_functions,
    const namespacet &ns);

  // function calls
  bool do_function_call_rec(
    const irep_idt &calling_function_identifier,
    locationt l_call,
    locationt l_return,
    const exprt &function,
    const exprt::operandst &arguments,
    const goto_functionst &goto_functions,
    const namespacet &ns);

  bool do_function_call(
    const irep_idt &calling_function_identifier,
    locationt l_call,
    locationt l_return,
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

  /// Get the state for the given location, creating it in a default way if it
  /// doesn't exist
  virtual statet &get_state(locationt l)=0;

  /// Get the state for the given location if it already exists; throw an
  /// exception if it doesn't
  virtual const statet &find_state(locationt l) const=0;

  /// Make a copy of a state
  virtual std::unique_ptr<statet> make_temporary_state(const statet &s)=0;
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
      throw std::out_of_range("failed to find state");

    return it->second;
  }

  const domainT &operator[](locationt l) const
  {
    typename state_mapt::const_iterator it=state_map.find(l);
    if(it==state_map.end())
      throw std::out_of_range("failed to find state");

    return it->second;
  }

  std::unique_ptr<statet> abstract_state_before(locationt t) const override
  {
    typename state_mapt::const_iterator it = state_map.find(t);
    if(it == state_map.end())
    {
      std::unique_ptr<statet> d = util_make_unique<domainT>();
      CHECK_RETURN(d->is_bottom());
      return d;
    }

    return util_make_unique<domainT>(it->second);
  }

  void clear() override
  {
    state_map.clear();
    ai_baset::clear();
  }

protected:
  typedef std::
    unordered_map<locationt, domainT, const_target_hash, pointee_address_equalt>
      state_mapt;
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
      throw std::out_of_range("failed to find state");

    return it->second;
  }

  bool merge(const statet &src, locationt from, locationt to) override
  {
    statet &dest=get_state(to);
    return static_cast<domainT &>(dest).merge(
      static_cast<const domainT &>(src), from, to);
  }

  std::unique_ptr<statet> make_temporary_state(const statet &s) override
  {
    return util_make_unique<domainT>(static_cast<const domainT &>(s));
  }

  void fixedpoint(
    const goto_functionst &goto_functions,
    const namespacet &ns) override
  {
    sequential_fixedpoint(goto_functions, ns);
  }

private:
  /// This function exists to enforce that `domainT` is derived from
  /// \ref ai_domain_baset
  void dummy(const domainT &s) { const statet &x=s; (void)x; }

  /// This function should not be implemented in sequential analyses
  bool merge_shared(const statet &, locationt, locationt, const namespacet &)
    override
  {
    throw "not implemented";
  }
};

template<typename domainT>
class concurrency_aware_ait:public ait<domainT>
{
public:
  using statet = typename ait<domainT>::statet;
  using locationt = typename statet::locationt;

  // constructor
  concurrency_aware_ait():ait<domainT>()
  {
  }

  bool merge_shared(
    const statet &src,
    locationt from,
    locationt to,
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
