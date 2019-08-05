/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// An interface for the storage of domains in the abstract interpreter.
/// Conceptually this is a map from location -> domain.
/// However in some cases we may wish to share domains between locations
/// so a simple map interface is not sufficient.
/// Also any domain that has not been previously accessed or stored is
/// automatically bottom.

#ifndef CPROVER_ANALYSES_AI_STORAGE_H
#define CPROVER_ANALYSES_AI_STORAGE_H

#include <goto-programs/goto_program.h>

#include "ai_domain.h"

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
  typedef goto_programt::const_targett locationt;

  /// Non-modifying access to the stored domains,
  /// used in the ai_baset public interface.
  /// In the case of un-analysed locals this should create a domain
  virtual std::shared_ptr<const statet> abstract_state_before(
    locationt l,
    const ai_domain_factory_baset &fac) const = 0;

  /// Look up the analysis state for a given location,
  /// instantiating a new domain if required.
  virtual statet &
  get_state(locationt l, const ai_domain_factory_baset &fac) = 0;

  /// Reset the abstract state
  virtual void clear()
  {
    return;
  }

  /// Notifies the storage that the user will not need the domain object(s)
  /// for this location.  After this has been called abstract_state_before may
  /// return an over-approximation of the value and get_state may give an
  /// under-approximation (forcing recomputation).
  virtual void prune(locationt l)
  {
    return;
  }
};

// A couple of older domains make direct use of the state map
class invariant_propagationt;
class dependence_grapht;

/// The most conventional storage; one domain per location
class location_sensitive_storaget : public ai_storage_baset
{
protected:
  typedef std::shared_ptr<statet> s_ptrt;

  /// This is location sensitive so we store one domain per location
  typedef std::
    unordered_map<locationt, s_ptrt, const_target_hash, pointee_address_equalt>
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
  std::shared_ptr<const statet> abstract_state_before(
    locationt l,
    const ai_domain_factory_baset &fac) const override
  {
    typename state_mapt::const_iterator it = state_map.find(l);
    if(it == state_map.end())
      return fac.make(l);

    return it->second;
  }

  statet &get_state(locationt l, const ai_domain_factory_baset &fac) override
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

  virtual void clear()
  {
    state_map.clear();
    return;
  }
};

#endif
