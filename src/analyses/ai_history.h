/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Abstract Interpretation history
///
/// This is an abstraction of the history of the program counter
/// / the history of the execution of the program.
/// It is used to track and control how the abstract interpreter
/// explores the program and for context sensitive analyses it is
/// also used as the key for the state map.
///
/// The abstract interpreter works with instances of ai_history_baset
/// (and history_ptrt's when dealing with storage) but this is just
/// an abstract interface much like ai_domain_baset, actual implementations
/// derive from it.

#ifndef CPROVER_ANALYSES_AI_HISTORY_H
#define CPROVER_ANALYSES_AI_HISTORY_H

#include <memory>

#include <goto-programs/goto_model.h>

#include <util/json.h>
#include <util/xml.h>

/// We make heavy use of reference counted pointers to history objects
class ai_history_baset;

class history_ptrt
{
public:
  typedef std::shared_ptr<const ai_history_baset> ptrt;

  history_ptrt(ptrt _p) : p(_p)
  {
  }

  history_ptrt(const ai_history_baset *h) : p(h)
  {
  }

  // Order and compare on the contents not the pointers
  bool operator<(const history_ptrt &op) const;
  bool operator==(const history_ptrt &op) const;

  const ai_history_baset &operator*(void) const
  {
    return *p;
  }

private:
  ptrt p;
};

/// This is the base interface; derive from this.
class ai_history_baset
{
public:
  typedef goto_programt::const_targett locationt;
  typedef irep_idt function_namet;

  ai_history_baset(const ai_history_baset &)
  {
  }

  /// Create a new history starting from a given location
  /// This is used to start the analysis from scratch
  /// PRECONDITION(l.is_dereferenceable());
  explicit ai_history_baset(locationt)
  {
  }

  enum class step_statust
  {
    NEW_FORCE_CONTINUE,
    NEW,
    MERGED,
    BLOCKED
  };

  typedef std::pair<step_statust, history_ptrt> step_returnt;
  typedef std::set<history_ptrt> history_sett;

  /// Step creates a new history by advancing the current one to location "to"
  /// It is given the set of all other histories that have reached this point.

  virtual step_returnt step(locationt to, history_sett &others) const = 0;

  /// PRECONDITION(to.is_dereferenceable());
  /// PRECONDITION(to in goto_program.get_successors(current_location()) ||
  ///              current_location()->is_function_call() ||
  ///              current_location()->is_end_function());
  ///
  /// Step may do one of four things :
  ///  1. Create a new history object in others and return a pointer to it.
  ///     Always adds the history to the worklist.
  ///     POSTCONDITION(IMPLIES(result.first ==step_statust::NEW_FORCE_CONTINUE,
  ///                           result.second is a new element of others));
  ///
  ///  2. Create a new history object in others and return a pointer to it.
  ///     Adds the history to the worklist if visit_edge increases the domain.
  ///     POSTCONDITION(IMPLIES(result.first == step_statust::NEW,
  ///                           result.second is a new element of others));
  ///
  ///  3. Merge with an existing history.
  ///     Will requeue the history if visit_edge increases the domain.
  ///     POSTCONDITION(IMPLIES(result.first == step_statust::MERGED,
  ///                           result.second is an element of others and
  ///                           others is unchanged));
  ///
  ///  4. Block this flow of execution (this may omit some program traces).
  ///     The abstract interpreter will skip this edge and not queue.
  ///     POSTCONDITION(IMPLIES(result.first == step_statust::BLOCKED,
  ///                           result.second == nullptr()));

  /// The order for history_sett
  virtual bool operator<(const ai_history_baset &op) const = 0;

  /// History objects should be comparable
  virtual bool operator==(const ai_history_baset &op) const = 0;

  /// The most recent location in the history
  /// POSTCONDITION(return value is dereferenceable)
  virtual const locationt &current_location(void) const = 0;

  /// Domains with a substantial height (such as intervals) may need to widen
  /// when merging this method allows the history to provide a hint on when to
  /// do this.
  virtual bool widen(const ai_history_baset &other) const
  {
    return false;
  }

  virtual void output(std::ostream &out) const = 0;
  virtual jsont output_json(void) const;
  virtual xmlt output_xml(void) const;
};

/// The common case of history is to only care about where you are now,
/// not how you got there!
/// Invariants are not checkable due to C++...
class ahistoricalt : public ai_history_baset
{
private:
  // DATA_INVARIANT(current.is_dereferenceable(), "Must not be _::end()")
  locationt current;

public:
  ahistoricalt(locationt i) : ai_history_baset(i), current(i)
  {
  }

  ahistoricalt(const ahistoricalt &old)
    : ai_history_baset(old), current(old.current)
  {
  }

  /// This will visit all reachable locations at least once.
  /// Locations will be visited more than once only when this is needed
  /// for convergence of the domains.
  step_returnt step(locationt to, history_sett &others) const override
  {
    if(others.empty())
    {
      history_ptrt next(new ahistoricalt(to));
      const auto r = others.insert(next);
      CHECK_RETURN(r.second);

      return std::make_pair(step_statust::NEW_FORCE_CONTINUE, next);
    }
    else
    {
      // Aggressively merge histories because they are indistinguishable
      INVARIANT(others.size() == 1, "Only needs one history per location");

      const auto it = others.begin();
      INVARIANT(
        (*(*it)).current_location() == to,
        "The history in the set others must be for that location to");

      return std::make_pair(step_statust::MERGED, *it);
    }
  }

  bool operator<(const ai_history_baset &op) const override
  {
    PRECONDITION(dynamic_cast<const ahistoricalt *>(&op) != nullptr);

    return this->current_location()->location_number <
           op.current_location()->location_number;
  }

  bool operator==(const ai_history_baset &op) const override
  {
    PRECONDITION(dynamic_cast<const ahistoricalt *>(&op) != nullptr);

    // It would be nice to:
    //  return this->current == op.current
    // But they may point to different goto_programs, undefined behaviour in C++
    // So (safe due to data invariant & uniqueness of location numbers) ...
    return this->current_location()->location_number ==
           op.current_location()->location_number;
  }

  const locationt &current_location(void) const override
  {
    return current;
  }

  // Use default widening
  // without history there is no reason to say any location is better than
  // another to widen.

  void output(std::ostream &out) const override
  {
    out << "ahistorical : location " << current_location()->location_number;
  }
};

#endif // CPROVER_ANALYSES_AI_HISTORY_H
