/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Abstract Interpretation history

#ifndef CPROVER_ANALYSES_AI_HISTORY_H
#define CPROVER_ANALYSES_AI_HISTORY_H

#include <memory>

#include <util/json.h>
#include <util/xml.h>

#include <goto-programs/goto_program.h>

/// A history object is an abstraction / representation of the control-flow
/// part of a set of traces.  The simplest example is a single
/// location which represents "all traces that reach this location".  More
/// sophisticated history objects represent "all traces that reach this point
/// after exactly N iterations of this loop", "all traces that follow a
/// given pattern of branching to reach this point" or "all traces that have
/// the following call stack and reach this location".
///
/// These are used to control the abstract interpreter; edges are computed
/// per history.  Depending on what storage is used, they may also control
/// or influence the number of domains that are used, supporting delayed
/// merging, loop unwinding, context dependent analysis, etc.

/// This is the base interface; derive from this.
class ai_history_baset
{
public:
  typedef goto_programt::const_targett locationt;

  /// History objects are intended to be immutable so they can be shared
  /// to reduce memory overhead
  typedef std::shared_ptr<const ai_history_baset> trace_ptrt;

protected:
  /// Create a new history starting from a given location
  /// This is used to start the analysis from scratch
  /// PRECONDITION(l.is_dereferenceable());
  explicit ai_history_baset(locationt)
  {
  }

  ai_history_baset(const ai_history_baset &)
  {
  }

public:
  virtual ~ai_history_baset()
  {
  }

  /// In a number of places we need to work with sets of histories
  /// so that these (a) make use of the immutability and sharing and
  /// (b) ownership can be transfered if necessary, we use shared pointers
  /// rather than references.
  /// One of the uses of this structure is as the work-list of the analyzer.
  /// Here the ordering of the set is very significant as it controls the
  /// order of exploration of the program.  This affects performance and in some
  /// cases it can affect the results.
  /// This custom comparison allows particular histories to control
  /// the order of exploration.
  struct compare_historyt
  {
    bool operator()(const trace_ptrt &l, const trace_ptrt &r) const
    {
      return *l < *r;
    }
  };
  typedef std::set<trace_ptrt, compare_historyt> trace_sett; // Order matters!

  enum class step_statust
  {
    NEW,
    MERGED,
    BLOCKED
  };

  typedef std::pair<step_statust, trace_ptrt> step_returnt;
  /// Step creates a new history by advancing the current one to location "to"
  /// It is given the set of all other histories that have reached this point.
  /// In the case of function call return it is also given the full history of
  /// the caller.  This allows function-local histories as they can "pick up"
  /// the state from before the call when computing the return edge.
  ///
  /// PRECONDITION(to.id_dereferenceable());
  /// PRECONDITION(to in goto_program.get_successors(current_location()) ||
  ///              current_location()->is_function_call() ||
  ///              current_location()->is_end_function());
  /// PRECONDITION(caller_hist == no_caller_history ||
  ///              current_location()->is_end_function);
  ///
  /// Step may do one of three things :
  ///  1. Create a new history object and return a pointer to it
  ///     This will force the analyser to continue regardless of domain changes
  ///     POSTCONDITION(IMPLIES(result.first == step_statust::NEW,
  ///                           result.second.use_count() == 1 ));
  ///  2. Merge with an existing history
  ///     This means the analyser will only continue if the domain is updated
  ///     POSTCONDITION(IMPLIES(result.first == step_statust::MERGED,
  ///                           result.second is an element of others));
  ///  3. Block this flow of execution
  ///     This indicates the transition is impossible (returning to a location
  ///     other than the call location) or undesireable (omitting some traces)
  ///     POSTCONDITION(IMPLIES(result.first == BLOCKED,
  ///                           result.second == nullptr()));
  virtual step_returnt step(
    locationt to,
    const trace_sett &others,
    trace_ptrt caller_hist) const = 0;

  static const trace_ptrt no_caller_history;

  /// The order for history_sett
  virtual bool operator<(const ai_history_baset &op) const = 0;

  /// History objects should be comparable
  virtual bool operator==(const ai_history_baset &op) const = 0;

  /// The current location in the history, used to compute the transformer
  /// POSTCONDITION(return value is dereferenceable)
  virtual const locationt &current_location(void) const = 0;

  /// Domains with a substantial height may need to widen when merging
  /// this method allows the history to provide a hint on when to do this
  /// The suggested use of this is for domains merge operation to check this
  /// and then widen in a domain specific way.  However it could be used in
  /// other ways (such as the transformer).  The key idea is that the history
  /// tracks / should know when to widen and when to continue.
  virtual bool should_widen(const ai_history_baset &other) const
  {
    return false;
  }

  virtual void output(std::ostream &out) const
  {
  }
  virtual jsont output_json(void) const;
  virtual xmlt output_xml(void) const;
};

/// The common case of history is to only care about where you are now,
/// not how you got there!
/// Invariants are not checkable due to C++...
class ahistoricalt : public ai_history_baset
{
protected:
  // DATA_INVARIANT(current.is_dereferenceable(), "Must not be _::end()")
  locationt current;

public:
  explicit ahistoricalt(locationt l) : ai_history_baset(l), current(l)
  {
  }

  ahistoricalt(const ahistoricalt &old)
    : ai_history_baset(old), current(old.current)
  {
  }

  step_returnt step(
    locationt to,
    const trace_sett &others,
    trace_ptrt caller_hist) const override
  {
    trace_ptrt next(new ahistoricalt(to));

    if(others.empty())
    {
      return std::make_pair(step_statust::NEW, next);
    }
    else
    {
      // Aggressively merge histories because they are indistinguishable
      INVARIANT(others.size() == 1, "Only needs one history per location");

      const auto it = others.begin();
      INVARIANT(
        *(*(it)) == *next,
        "The next location in history map must contain next history");

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
    // But they may point to different goto_programs,
    // giving undefined behaviour in C++
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
  bool should_widen(const ai_history_baset &other) const override
  {
    return ai_history_baset::should_widen(other);
  }

  void output(std::ostream &out) const override
  {
    out << "ahistorical : location " << current_location()->location_number;
  }
};


/// As more detailed histories can get complex (for example, nested loops
/// or deep, mutually recursive call stacks) they often need some user
/// controls or limits.  The best way to do this is to give the limits to
/// the first, start-of-history object and let it propagate.  Having a
/// factory gives a way of wrapping this information up in a common interface
class ai_history_factory_baset
{
public:
  /// Creates a new history from the given starting point
  virtual ai_history_baset::trace_ptrt epoch(ai_history_baset::locationt) = 0;

  virtual ~ai_history_factory_baset()
  {
  }
};

/// An easy factory implementation for histories that don't need parameters
template <typename traceT>
class ai_history_factory_default_constructort : public ai_history_factory_baset
{
public:
  ai_history_baset::trace_ptrt epoch(ai_history_baset::locationt l) override
  {
    ai_history_baset::trace_ptrt p(new traceT(l));
    return p;
  }
};

#endif // CPROVER_ANALYSES_AI_HISTORY_H
