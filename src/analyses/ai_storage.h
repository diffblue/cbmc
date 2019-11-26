/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Abstract Interpretation Storage
///
/// An interface for the storage of domains in the abstract interpreter.
/// Conceptually this is a map from history -> domain.
/// However in some cases we may wish to share domains between locations
/// so a simple map interface is not sufficient.
/// Also any domain that has not been previously accessed or stored is
/// automatically bottom.
/// There is a constant interface which returns shared pointers to const
/// domains, allowing these to either be stored domains, or things created
/// on-the-fly.  The non-constant interace returns a reference as it can
/// create and initialise the domains as needed.

#ifndef CPROVER_ANALYSES_AI_STORAGE_H
#define CPROVER_ANALYSES_AI_STORAGE_H

#include <goto-programs/goto_program.h>

#include "ai_domain.h"
#include "ai_history.h"

/// This is the basic interface for storing domains.
/// The abstract interpreters should use this interface by default.
class ai_storage_baset
{
protected:
  ai_storage_baset()
  {
  }

public:
  virtual ~ai_storage_baset()
  {
  }

  typedef ai_domain_baset statet;
  typedef std::shared_ptr<statet> state_ptrt;
  typedef std::shared_ptr<const statet> cstate_ptrt;
  typedef ai_history_baset tracet;
  typedef ai_history_baset::trace_ptrt trace_ptrt;
  typedef ai_history_baset::trace_sett trace_sett;
  typedef std::shared_ptr<trace_sett> trace_set_ptrt;
  typedef std::shared_ptr<const trace_sett> ctrace_set_ptrt;
  typedef goto_programt::const_targett locationt;

  /// Returns all of the histories that have reached
  /// the start of the instruction.
  virtual ctrace_set_ptrt abstract_traces_before(locationt l) const = 0;

  /// Non-modifying access to the stored domains,
  /// used in the ai_baset public interface.
  /// In the case of un-analysed locals this should create a domain
  /// The history version is the primary version, the location one may
  /// simply join all of the histories that reach the given location
  virtual cstate_ptrt abstract_state_before(
    trace_ptrt p,
    const ai_domain_factory_baset &fac) const = 0;

  virtual cstate_ptrt abstract_state_before(
    locationt l,
    const ai_domain_factory_baset &fac) const = 0;

  /// Look up the analysis state for a given history,
  /// instantiating a new domain if required.
  virtual statet &
  get_state(trace_ptrt p, const ai_domain_factory_baset &fac) = 0;

  /// Reset the abstract state
  virtual void clear()
  {
    return;
  }

  /// Notifies the storage that the user will not need the domain object(s)
  /// for this location.  After this has been called abstract_state_before may
  /// return an over-approximation of the value and get_state may give an
  /// under-approximation (forcing recomputation).
  /// If there are multiple histories that reach this location all will be
  /// affected
  virtual void prune(locationt l)
  {
    return;
  }
};

// There are a number of options for how to store the history objects.
// This implements a simple one.  It is not in ai_storage_baset so that
// storage implementations can implement their own, more specific, approaches
class trace_map_storaget : public ai_storage_baset
{
protected:
  typedef std::map<locationt, trace_set_ptrt> trace_mapt;
  trace_mapt trace_map;

  // This retains one part of a shared_ptr to the history object
  void register_trace(trace_ptrt p)
  {
    // Save the trace_ptrt
    trace_mapt::iterator it = trace_map.find(p->current_location());
    if(it == trace_map.end())
    {
      trace_set_ptrt s(new trace_sett());
      auto ins = trace_map.emplace(p->current_location(), s);
      CHECK_RETURN(ins.second);
      it = ins.first;
    }
    // Strictly this should be "it->second points to a trace_set"
    POSTCONDITION(it->second != nullptr);

    it->second->insert(p);

    return;
  }

public:
  ctrace_set_ptrt abstract_traces_before(locationt l) const override
  {
    trace_mapt::const_iterator it = trace_map.find(l);
    if(it == trace_map.end())
      return trace_set_ptrt(new trace_sett());

    // Strictly this should be "it->second points to a trace_set"
    POSTCONDITION(it->second != nullptr);
    return it->second;
  }

  void clear() override
  {
    ai_storage_baset::clear();
    trace_map.clear();
    return;
  }
};

// A couple of older domains make direct use of the state map
class invariant_propagationt;
class dependence_grapht;

/// The most conventional storage; one domain per location
class location_sensitive_storaget : public trace_map_storaget
{
protected:
  /// This is location sensitive so we store one domain per location
  typedef std::unordered_map<
    locationt,
    state_ptrt,
    const_target_hash,
    pointee_address_equalt>
    state_mapt;
  state_mapt state_map;

  // Support some older domains that explicitly iterate across the state map
  friend invariant_propagationt;
  friend dependence_grapht;
  state_mapt &internal(void)
  {
    return state_map;
  }

public:
  cstate_ptrt abstract_state_before(
    trace_ptrt p,
    const ai_domain_factory_baset &fac) const override
  {
    return abstract_state_before(p->current_location(), fac);
  }

  cstate_ptrt abstract_state_before(
    locationt l,
    const ai_domain_factory_baset &fac) const override
  {
    typename state_mapt::const_iterator it = state_map.find(l);
    if(it == state_map.end())
      return fac.make(l);

    return it->second;
  }

  statet &get_state(trace_ptrt p, const ai_domain_factory_baset &fac) override
  {
    register_trace(p);
    return get_state(p->current_location(), fac);
  }

  // For backwards compatability
  // Care should be exercised in using this.  It is possible to create domains
  // without any corresponding history object(s).  This can lead to somewhat
  // unexpected behaviour depending on which APIs you use.
  DEPRECATED(SINCE(2019, 08, 01, "use get_state(trace_ptrt p) instead"))
  statet &get_state(locationt l, const ai_domain_factory_baset &fac)
  {
    typename state_mapt::const_iterator it = state_map.find(l);
    if(it == state_map.end())
    {
      std::shared_ptr<statet> d(fac.make(l));
      auto p = state_map.emplace(l, d);
      CHECK_RETURN(p.second);
      it = p.first;
    }

    return *(it->second);
  }

  void clear() override
  {
    trace_map_storaget::clear();
    state_map.clear();
    return;
  }
};

// The most precise form of storage
class history_sensitive_storaget : public trace_map_storaget
{
protected:
  typedef std::map<trace_ptrt, state_ptrt, ai_history_baset::compare_historyt>
    domain_mapt;
  domain_mapt domain_map;

public:
  cstate_ptrt abstract_state_before(
    trace_ptrt p,
    const ai_domain_factory_baset &fac) const override
  {
    auto it = domain_map.find(p);
    if(it == domain_map.end())
      return fac.make(p->current_location());

    return it->second;
  }

  cstate_ptrt abstract_state_before(
    locationt t,
    const ai_domain_factory_baset &fac) const override
  {
    auto traces = abstract_traces_before(t);

    if(traces->size() == 0)
    {
      return fac.make(t);
    }
    else if(traces->size() == 1)
    {
      auto it = domain_map.find(*(traces->begin()));
      DATA_INVARIANT(
        it != domain_map.end(), "domain_map must be in sync with trace_map");
      return it->second;
    }
    else
    {
      // Need to merge all of the traces that reach this location
      auto res = fac.make(t);

      for(auto p : *traces)
      {
        auto it = domain_map.find(p);
        DATA_INVARIANT(
          it != domain_map.end(), "domain_map must be in sync with trace_map");
        fac.merge(*res, *(it->second), p, p);
      }

      return cstate_ptrt(res.release());
    }
  }

  statet &get_state(trace_ptrt p, const ai_domain_factory_baset &fac) override
  {
    register_trace(p);

    auto it = domain_map.find(p);
    if(it == domain_map.end())
    {
      std::shared_ptr<statet> d(fac.make(p->current_location()));
      auto jt = domain_map.emplace(p, d);
      CHECK_RETURN(jt.second);
      it = jt.first;
    }

    return *(it->second);
  }

  void clear() override
  {
    trace_map_storaget::clear();
    domain_map.clear();
    return;
  }
};

#endif
