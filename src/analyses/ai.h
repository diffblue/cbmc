/*******************************************************************\

Module: Abstract Interpretation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstract Interpretation
///
/// This is the core of the abstract interpretation framework.
/// To run an analysis you need four components:
///
///  1. An abstract interpreter, derived from ai_baset.
///     This performs that actual analysis.  There are a number of alternative
///     to choose from, primarily giving different ways of handling function
///     calls / interprocedural analysis.
///     More information is given in this file.
///
///  2. A history factory, derived from ai_history_factory_baset.
///     This generates history objects (derived from ai_history_baset) which
///     control the number of steps that the analysis performs.  These can be
///     simple, just tracking location, or they can be complex, tracking
///     location, function calls, branches (forwards and backwards), even
///     threading.
///     See ai_history.h for more information.
///
///  3. A domain factory, derived from ai_domain_factory_baset.
///     This generates domain objects (derived from ai_domain_baset) which
///     represent the sets of possible valuations that the variables can take at
///     a given point (given history).  These can be very simple, just tracking
///     whether a location is reachable or not, or they can be very
///     sophisticated tracking relations between variables, pointers, etc.
///     See ai_domain.h for more information.
///
///  4. A storage object, derived from ai_storage_baset.
///     This stores the history and domain objects and manages the link.
///     The simplest case is to store one domain per history
///     (see history_sensitive_storaget).  However this can require a large
///     amount of memory being used, so there are options to share / merge
///     domains between different histories, reducing precision in return for
///     better performance.

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
#include "ai_history.h"
#include "ai_storage.h"
#include "is_threaded.h"

/// This is the basic interface of the abstract interpreter with default
/// implementations of the core functionality.
///
/// Users of abstract interpreters should use the interface given by this class.
/// It breaks into three categories:
///
/// 1. Running an analysis, via
///    \ref ai_baset#operator()(const irep_idt&,const goto_programt&, <!--
///    --> const namespacet&),
///    \ref ai_baset#operator()(const goto_functionst&,const namespacet&)
///    and \ref ai_baset#operator()(const abstract_goto_modelt&)
/// 2. Accessing the results of an analysis, by looking up the history objects
///    for a given location \p l using
///    \ref ai_baset#abstract_traces_before(locationt)const
///    or the domains using
///    \ref ai_baset#abstract_state_before(locationt)const
/// 3. Outputting the results of the analysis; see
///    \ref ai_baset#output(const namespacet&, const irep_idt&,
///    const goto_programt&, std::ostream&)const et cetera.
///
/// Where possible, uses should be agnostic of the particular configuration of
/// the abstract interpreter.  The "tasks" that goto-analyze uses are good
/// examples of how to do this.
///
/// From a development point of view, there are several directions in which
/// this can be extended by inheriting from ai_baset or one of its children:
///
/// A. To change how single edges are computed
///    \ref ait#visit_edge and \ref ait#visit_edge_function_call
///    ai_recursive_interproceduralt uses this to recurse to evaluate
///    function calls rather than approximating them as ai_baset does.
///
/// B. To change how individual instructions are handled
///    \ref ait#visit() and related functions.
///
/// C. To change the way that the fixed point is computed
///    \ref ait#fixedpoint()
///    concurrency_aware_ait does this to compute a fixed point over threads.
///
/// D. For pre-analysis initialization
///    \ref ait#initialize(const irep_idt&, const goto_programt&),
///    \ref ait#initialize(const irep_idt&,
///    const goto_functionst::goto_functiont&) and
///    \ref ait#initialize(const goto_functionst&),
///
/// E. For post-analysis cleanup
///    \ref ait#finalize(),
///
/// Historically, uses of abstract interpretation inherited from ait<domainT>
/// and added the necessary functionality.  This works (although care must be
/// taken to respect the APIs of the various components -- there are some hacks
/// to support older analyses that didn't) but is discouraged in favour of
/// having an object for the abstract interpreter and using its public API.

class ai_baset
{
public:
  typedef ai_domain_baset statet;
  typedef ai_storage_baset::cstate_ptrt cstate_ptrt;
  typedef ai_history_baset::trace_ptrt trace_ptrt;
  typedef ai_history_baset::trace_sett trace_sett;
  typedef ai_storage_baset::ctrace_set_ptrt ctrace_set_ptrt;
  typedef goto_programt::const_targett locationt;

  ai_baset(
    std::unique_ptr<ai_history_factory_baset> &&hf,
    std::unique_ptr<ai_domain_factory_baset> &&df,
    std::unique_ptr<ai_storage_baset> &&st)
    : history_factory(std::move(hf)),
      domain_factory(std::move(df)),
      storage(std::move(st))
  {
  }

  virtual ~ai_baset()
  {
  }

  /// Run abstract interpretation on a single function
  void operator()(
    const irep_idt &function_id,
    const goto_programt &goto_program,
    const namespacet &ns)
  {
    goto_functionst goto_functions;
    initialize(function_id, goto_program);
    trace_ptrt p = entry_state(goto_program);
    fixedpoint(p, function_id, goto_program, goto_functions, ns);
    finalize();
  }

  /// Run abstract interpretation on a whole program
  void operator()(
    const goto_functionst &goto_functions,
    const namespacet &ns)
  {
    initialize(goto_functions);
    trace_ptrt p = entry_state(goto_functions);
    fixedpoint(p, goto_functions, ns);
    finalize();
  }

  /// Run abstract interpretation on a whole program
  void operator()(const abstract_goto_modelt &goto_model)
  {
    const namespacet ns(goto_model.get_symbol_table());
    initialize(goto_model.get_goto_functions());
    trace_ptrt p = entry_state(goto_model.get_goto_functions());
    fixedpoint(p, goto_model.get_goto_functions(), ns);
    finalize();
  }

  /// Run abstract interpretation on a single function
  void operator()(
    const irep_idt &function_id,
    const goto_functionst::goto_functiont &goto_function,
    const namespacet &ns)
  {
    goto_functionst goto_functions;
    initialize(function_id, goto_function);
    trace_ptrt p = entry_state(goto_function.body);
    fixedpoint(p, function_id, goto_function.body, goto_functions, ns);
    finalize();
  }

  /// Returns all of the histories that have reached
  /// the start of the instruction.
  /// PRECONDITION(l is dereferenceable)
  /// \param l: The location before which we want the set of histories
  /// \return The set of histories before `l`.
  virtual ctrace_set_ptrt abstract_traces_before(locationt l) const
  {
    return storage->abstract_traces_before(l);
  }

  /// Returns all of the histories that have reached
  /// the end of the instruction.
  /// PRECONDITION(l is dereferenceable)
  /// \param l: The location before which we want the set of histories
  /// \return The set of histories before `l`.
  virtual ctrace_set_ptrt abstract_traces_after(locationt l) const
  {
    /// PRECONDITION(l is dereferenceable && std::next(l) is dereferenceable)
    /// Check relies on a DATA_INVARIANT of goto_programs
    INVARIANT(!l->is_end_function(), "No state after the last instruction");
    return storage->abstract_traces_before(std::next(l));
  }

  /// Get a copy of the abstract state before the given instruction, without
  /// needing to know what kind of domain or history is used. Note: intended
  /// for users of the abstract interpreter; derived classes should
  /// use \ref get_state to access the actual underlying state.
  /// PRECONDITION(l is dereferenceable)
  /// \param l: The location before which we want the abstract state
  /// \return The abstract state before `l`. We return a pointer to a copy as
  ///   the method should be const and there are some non-trivial cases
  ///   including merging abstract states, etc.
  virtual cstate_ptrt abstract_state_before(locationt l) const
  {
    return storage->abstract_state_before(l, *domain_factory);
  }

  /// Get a copy of the abstract state after the given instruction, without
  /// needing to know what kind of domain or history is used. Note: intended
  /// for users of the abstract interpreter; derived classes should
  /// use \ref get_state to access the actual underlying state.
  /// \param l: The location before which we want the abstract state
  /// \return The abstract state after `l`. We return a pointer to a copy as
  ///   the method should be const and there are some non-trivial cases
  ///   including merging abstract states, etc.
  virtual cstate_ptrt abstract_state_after(locationt l) const
  {
    /// PRECONDITION(l is dereferenceable && std::next(l) is dereferenceable)
    /// Check relies on a DATA_INVARIANT of goto_programs
    INVARIANT(!l->is_end_function(), "No state after the last instruction");
    return abstract_state_before(std::next(l));
  }

  /// The same interfaces but with histories
  virtual cstate_ptrt abstract_state_before(const trace_ptrt &p) const
  {
    return storage->abstract_state_before(p, *domain_factory);
  }

  virtual cstate_ptrt abstract_state_after(const trace_ptrt &p) const
  {
    locationt l = p->current_location();
    INVARIANT(!l->is_end_function(), "No state after the last instruction");

    locationt n = std::next(l);

    auto step_return = p->step(n, *(storage->abstract_traces_before(n)));

    return storage->abstract_state_before(step_return.second, *domain_factory);
  }

  /// Reset the abstract state
  virtual void clear()
  {
    storage->clear();
  }

  /// Output the abstract states for a single function
  /// \param ns: The namespace
  /// \param function_id: The identifier used to find a symbol to
  ///   identify the \p goto_program's source language
  /// \param goto_program: The goto program
  /// \param out: The ostream to direct output to
  virtual void output(
    const namespacet &ns,
    const irep_idt &function_id,
    const goto_programt &goto_program,
    std::ostream &out) const;

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
    const goto_functionst::goto_functiont &goto_function,
    std::ostream &out) const
  {
    output(ns, irep_idt(), goto_function.body, out);
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
    return output_json(ns, irep_idt(), goto_program);
  }

  /// Output the abstract states for a single function as JSON
  jsont output_json(
    const namespacet &ns,
    const goto_functionst::goto_functiont &goto_function) const
  {
    return output_json(ns, irep_idt(), goto_function.body);
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
    return output_xml(ns, irep_idt(), goto_program);
  }

  /// Output the abstract states for a single function as XML
  xmlt output_xml(
    const namespacet &ns,
    const goto_functionst::goto_functiont &goto_function) const
  {
    return output_xml(ns, irep_idt(), goto_function.body);
  }

protected:
  /// Initialize all the abstract states for a single function. Override this to
  /// do custom per-domain initialization.
  virtual void
  initialize(const irep_idt &function_id, const goto_programt &goto_program);

  /// Initialize all the abstract states for a single function.
  virtual void initialize(
    const irep_idt &function_id,
    const goto_functionst::goto_functiont &goto_function);

  /// Initialize all the abstract states for a whole program. Override this to
  /// do custom per-analysis initialization.
  virtual void initialize(const goto_functionst &goto_functions);

  /// Override this to add a cleanup or post-processing step after fixedpoint
  /// has run
  virtual void finalize();

  /// Set the abstract state of the entry location of a single function to the
  /// entry state required by the analysis
  trace_ptrt entry_state(const goto_programt &goto_program);

  /// Set the abstract state of the entry location of a whole program to the
  /// entry state required by the analysis
  trace_ptrt entry_state(const goto_functionst &goto_functions);

  /// Output the abstract states for a single function as JSON
  /// \param ns: The namespace
  /// \param goto_program: The goto program
  /// \param function_id: The identifier used to find a symbol to
  ///   identify the source language
  /// \return The JSON object
  virtual jsont output_json(
    const namespacet &ns,
    const irep_idt &function_id,
    const goto_programt &goto_program) const;

  /// Output the abstract states for a single function as XML
  /// \param ns: The namespace
  /// \param goto_program: The goto program
  /// \param function_id: The identifier used to find a symbol to
  ///   identify the source language
  /// \return The XML object
  virtual xmlt output_xml(
    const namespacet &ns,
    const irep_idt &function_id,
    const goto_programt &goto_program) const;

  /// The work queue, sorted using the history's ordering operator
  typedef trace_sett working_sett;

  /// Get the next location from the work queue
  trace_ptrt get_next(working_sett &working_set);

  void put_in_working_set(working_sett &working_set, trace_ptrt t)
  {
    working_set.insert(t);
  }

  /// Run the fixedpoint algorithm until it reaches a fixed point
  /// \return True if we found something new
  virtual bool fixedpoint(
    trace_ptrt starting_trace,
    const irep_idt &function_id,
    const goto_programt &goto_program,
    const goto_functionst &goto_functions,
    const namespacet &ns);

  virtual void fixedpoint(
    trace_ptrt starting_trace,
    const goto_functionst &goto_functions,
    const namespacet &ns);

  /// Perform one step of abstract interpretation from trace t
  /// Depending on the instruction type it may compute a number of "edges"
  /// or applications of the abstract transformer
  /// \return True if the state was changed
  virtual bool visit(
    const irep_idt &function_id,
    trace_ptrt p,
    working_sett &working_set,
    const goto_programt &goto_program,
    const goto_functionst &goto_functions,
    const namespacet &ns);

  // function calls and return are special cases
  // different kinds of analysis handle these differently so these are virtual
  // visit_function_call handles which function(s) to call,
  // while visit_edge_function_call handles a single call
  virtual bool visit_function_call(
    const irep_idt &function_id,
    trace_ptrt p_call,
    working_sett &working_set,
    const goto_programt &goto_program,
    const goto_functionst &goto_functions,
    const namespacet &ns);

  virtual bool visit_end_function(
    const irep_idt &function_id,
    trace_ptrt p,
    working_sett &working_set,
    const goto_programt &goto_program,
    const goto_functionst &goto_functions,
    const namespacet &ns);

  // The most basic step, computing one edge / transformer application.
  bool visit_edge(
    const irep_idt &function_id,
    trace_ptrt p,
    const irep_idt &to_function_id,
    locationt to_l,
    const namespacet &ns,
    working_sett &working_set);

  virtual bool visit_edge_function_call(
    const irep_idt &calling_function_id,
    trace_ptrt p_call,
    locationt l_return,
    const irep_idt &callee_function_id,
    working_sett &working_set,
    const goto_programt &callee,
    const goto_functionst &goto_functions,
    const namespacet &ns);

  /// For creating history objects
  std::unique_ptr<ai_history_factory_baset> history_factory;

  /// For creating domain objects
  std::unique_ptr<ai_domain_factory_baset> domain_factory;

  /// Merge the state \p src, flowing from tracet \p from to
  /// tracet \p to, into the state currently stored for tracet \p to.
  virtual bool merge(const statet &src, trace_ptrt from, trace_ptrt to)
  {
    statet &dest = get_state(to);
    return domain_factory->merge(dest, src, from, to);
  }

  /// Make a copy of a state
  virtual std::unique_ptr<statet> make_temporary_state(const statet &s)
  {
    return domain_factory->copy(s);
  }

  // Domain and history storage
  std::unique_ptr<ai_storage_baset> storage;

  /// Get the state for the given history, creating it with the factory if it
  /// doesn't exist
  virtual statet &get_state(trace_ptrt p)
  {
    return storage->get_state(p, *domain_factory);
  }
};

// Perform interprocedural analysis by simply recursing in the interpreter
// This can lead to a call stack overflow if the domain has a large height
class ai_recursive_interproceduralt : public ai_baset
{
public:
  ai_recursive_interproceduralt(
    std::unique_ptr<ai_history_factory_baset> &&hf,
    std::unique_ptr<ai_domain_factory_baset> &&df,
    std::unique_ptr<ai_storage_baset> &&st)
    : ai_baset(std::move(hf), std::move(df), std::move(st))
  {
  }

protected:
  // Override the function that handles a single function call edge
  bool visit_edge_function_call(
    const irep_idt &calling_function_id,
    trace_ptrt p_call,
    locationt l_return,
    const irep_idt &callee_function_id,
    working_sett &working_set,
    const goto_programt &callee,
    const goto_functionst &goto_functions,
    const namespacet &ns) override;
};

/// ait supplies three of the four components needed: an abstract interpreter
/// (in this case handling function calls via recursion), a history factory
/// (using the simplest possible history objects) and storage (one domain per
/// location).  The fourth component, the domain, is provided by the template
/// parameter.  This is gives a "classical" abstract interpreter and is
/// backwards compatible with older code.
///
/// \tparam domainT A type derived from ai_domain_baset that represents the
///     values in the AI domain
template <typename domainT>
class ait : public ai_recursive_interproceduralt
{
public:
  // constructor
  ait()
    : ai_recursive_interproceduralt(
        util_make_unique<
          ai_history_factory_default_constructort<ahistoricalt>>(),
        util_make_unique<ai_domain_factory_default_constructort<domainT>>(),
        util_make_unique<location_sensitive_storaget>())
  {
  }

  explicit ait(std::unique_ptr<ai_domain_factory_baset> &&df)
    : ai_recursive_interproceduralt(
        util_make_unique<
          ai_history_factory_default_constructort<ahistoricalt>>(),
        std::move(df),
        util_make_unique<location_sensitive_storaget>())
  {
  }

  typedef goto_programt::const_targett locationt;

  /// Find the analysis result for a given location.
  // The older interface for non-modifying access
  // Not recommended as it will throw an exception if a location has not
  // been reached in an analysis and there is no (other) way of telling
  // if a location has been reached.
  DEPRECATED(SINCE(2019, 08, 01, "use abstract_state_{before,after} instead"))
  const domainT &operator[](locationt l) const
  {
    auto p = storage->abstract_state_before(l, *domain_factory);

    if(p.use_count() == 1)
    {
      // Would be unsafe to return the dereferenced object
      throw std::out_of_range("failed to find state");
    }

    return static_cast<const domainT &>(*p);
  }

protected:
  // Support the legacy get_state interface which is needed for a few domains
  // This is one of the few users of the legacy get_state(locationt) method
  // in location_sensitive_storaget.
  DEPRECATED(SINCE(2019, 08, 01, "use get_state(trace_ptrt p) instead"))
  virtual statet &get_state(locationt l)
  {
    auto &s = dynamic_cast<location_sensitive_storaget &>(*storage);
    return s.get_state(l, *domain_factory);
  }

  using ai_baset::get_state;

private:
  /// This function exists to enforce that `domainT` is derived from
  /// \ref ai_domain_baset
  void dummy(const domainT &s) { const statet &x=s; (void)x; }
};

/// Base class for concurrency-aware abstract interpretation. See
/// \ref ait for details.
/// The only difference is that after the sequential fixed point construction,
/// as done by \ref ait, another step is added to account for
/// concurrently-executed instructions.
/// Basically, it makes the analysis flow-insensitive by feeding results of a
/// sequential execution back into the entry point, thereby accounting for any
/// values computed by different threads. Compare
/// [Martin Rinard, "Analysis of Multi-Threaded Programs", SAS 2001](
/// http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.28.4747&<!--
/// -->rep=rep1&type=pdf).
///
/// \tparam domainT A type derived from ai_domain_baset that represents the
///     values in the AI domain
///
/// It is important to note that the domains used by this need an extra merge
/// method, but, far more critically, they need the property that it is not
/// possible to "undo" changes to the domain.  Tracking last modified location
/// has this property, numerical domains such as constants and intervals do not
/// and using this kind of concurrent analysis for these domains may miss
/// significant behaviours.
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
  explicit concurrency_aware_ait(std::unique_ptr<ai_domain_factory_baset> &&df)
    : ait<domainT>(std::move(df))
  {
  }

  virtual bool merge_shared(
    const statet &src,
    locationt from,
    locationt to,
    const namespacet &ns)
  {
    statet &dest=this->get_state(to);
    return static_cast<domainT &>(dest).merge_shared(
      static_cast<const domainT &>(src), from, to, ns);
  }

protected:
  using working_sett = ai_baset::working_sett;

  void fixedpoint(
    ai_baset::trace_ptrt start_trace,
    const goto_functionst &goto_functions,
    const namespacet &ns) override
  {
    ai_baset::fixedpoint(start_trace, goto_functions, ns);

    is_threadedt is_threaded(goto_functions);

    // construct an initial shared state collecting the results of all
    // functions
    goto_programt tmp;
    tmp.add_instruction();
    goto_programt::const_targett sh_target = tmp.instructions.begin();
    ai_baset::trace_ptrt target_hist =
      ai_baset::history_factory->epoch(sh_target);
    statet &shared_state = ait<domainT>::get_state(sh_target);

    struct wl_entryt
    {
      wl_entryt(
        const irep_idt &_function_id,
        const goto_programt &_goto_program,
        locationt _location)
        : function_id(_function_id),
          goto_program(&_goto_program),
          location(_location)
      {
      }

      irep_idt function_id;
      const goto_programt *goto_program;
      locationt location;
    };

    typedef std::list<wl_entryt> thread_wlt;
    thread_wlt thread_wl;

    forall_goto_functions(it, goto_functions)
      forall_goto_program_instructions(t_it, it->second.body)
      {
        if(is_threaded(t_it))
        {
          thread_wl.push_back(wl_entryt(it->first, it->second.body, t_it));

          goto_programt::const_targett l_end =
            it->second.body.instructions.end();
          --l_end;

          merge_shared(shared_state, l_end, sh_target, ns);
        }
      }

    // now feed in the shared state into all concurrently executing
    // functions, and iterate until the shared state stabilizes
    bool new_shared = true;
    while(new_shared)
    {
      new_shared = false;

      for(const auto &wl_entry : thread_wl)
      {
        working_sett working_set;
        ai_baset::trace_ptrt t(
          ai_baset::history_factory->epoch(wl_entry.location));
        ai_baset::put_in_working_set(working_set, t);

        statet &begin_state = ait<domainT>::get_state(wl_entry.location);
        ait<domainT>::merge(begin_state, target_hist, t);

        while(!working_set.empty())
        {
          ai_baset::trace_ptrt p = ai_baset::get_next(working_set);
          goto_programt::const_targett l = p->current_location();

          ai_baset::visit(
            wl_entry.function_id,
            p,
            working_set,
            *(wl_entry.goto_program),
            goto_functions,
            ns);

          // the underlying domain must make sure that the final state
          // carries all possible values; otherwise we would need to
          // merge over each and every state
          if(l->is_end_function())
            new_shared |= merge_shared(shared_state, l, sh_target, ns);
        }
      }
    }
  }
};

#endif // CPROVER_ANALYSES_AI_H
