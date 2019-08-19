/*******************************************************************\

Module: Abstract Interpretation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstract Interpretation Domain
///
/// An abstract domain is an over-approximation of a set of possible valuations
/// that the variables in a program may take at a given point in the program.
/// For example if you have two variables, x and y and at a given point they
/// can take the following values:
///
///  (x = 1, y = -1),   (x = -1, y = -1),   (x = 1, y = 0)
///
/// then you could represent this with a pair of intervals:
///
///   x in [-1,1],  y in [-1,0]
///
/// this is an over-approximation as it also describes valuations, like,
/// (x = 0, y = 0) which are not in the set.  It also omits things like the
/// link between the variables, such as knowning x >= y.
/// However, in return for some imprecision (in a known direction), it gains
/// scalability.  A pair of intervals can represent sets of valuations that
/// might contain millions or billions of pairs.
///
/// The abstract interpretation framework is modular in terms of the domain
/// used.  Inherit from ai_domain_baset, implement the pure virtual functions
/// and add a merge method and your domain can be plugged in to the analysis.
/// The actual "glue" is a factory so that you can have domains with non-trivial
/// constructors.  These inherit from ai_domain_factory_baset, but
/// ai_domain_factory_default_constructort<your_domain> will be fine if the
/// default constructor is fine and inheriting from
/// ai_domain_factoryt<your_domain> will be fine if non-trivial constructors
/// are needed.

#ifndef CPROVER_ANALYSES_AI_DOMAIN_H
#define CPROVER_ANALYSES_AI_DOMAIN_H

#include <util/expr.h>
#include <util/json.h>
#include <util/make_unique.h>
#include <util/xml.h>

#include <goto-programs/goto_model.h>

#include "ai_history.h"

// forward reference the abstract interpreter interface
class ai_baset;

/// The interface offered by a domain, allows code to manipulate domains without
/// knowing their exact type.  Derive from this to implement domains.
class ai_domain_baset
{
protected:
  /// The constructor is expected to produce 'false' or 'bottom'
  /// A default constructor is not part of the domain interface
  ai_domain_baset()
  {
  }

  /// A copy constructor is part of the domain interface
  ai_domain_baset(const ai_domain_baset &old)
  {
  }

public:
  virtual ~ai_domain_baset()
  {
  }

  typedef goto_programt::const_targett locationt;
  typedef ai_history_baset::trace_ptrt trace_ptrt;

  /// how function calls are treated:
  /// a) there is an edge from each call site to the function head
  /// b) there is an edge from the last instruction (END_FUNCTION)
  ///    of the function to the instruction _following_ the call site
  ///    (this also needs to set the LHS, if applicable)
  ///
  /// in some cases, function calls are skipped, in which case:
  /// c) there is an edge from the call instruction to the instruction after
  ///
  /// "this" is the domain before the instruction "from"
  /// "from" is the instruction to be interpreted
  /// "to" is the next instruction (for GOTO, FUNCTION_CALL, END_FUNCTION)
  ///
  /// PRECONDITION(from.is_dereferenceable(), "Must not be _::end()")
  /// PRECONDITION(to.is_dereferenceable(), "Must not be _::end()")
  /// PRECONDITION(are_comparable(from,to) ||
  ///              (from->is_function_call() || from->is_end_function())
  ///
  /// The history aware version is used by the abstract interpreter
  /// for backwards compatability it calls the older signature
  virtual void transform(
    const irep_idt &function_from,
    trace_ptrt from,
    const irep_idt &function_to,
    trace_ptrt to,
    ai_baset &ai,
    const namespacet &ns)
  {
    return transform(
      function_from,
      from->current_location(),
      function_to,
      to->current_location(),
      ai,
      ns);
  }

  DEPRECATED(SINCE(2019, 08, 01, "use the history signature instead"))
  virtual void transform(
    const irep_idt &function_from,
    locationt from,
    const irep_idt &function_to,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) = 0;

  virtual void
  output(std::ostream &, const ai_baset &, const namespacet &) const
  {
  }

  virtual jsont output_json(const ai_baset &ai, const namespacet &ns) const;

  virtual xmlt output_xml(const ai_baset &ai, const namespacet &ns) const;

  /// no states
  virtual void make_bottom() = 0;

  /// all states -- the analysis doesn't use this,
  /// and domains may refuse to implement it.
  virtual void make_top() = 0;

  /// Make this domain a reasonable entry-point state
  virtual void make_entry() = 0;

  virtual bool is_bottom() const = 0;

  virtual bool is_top() const = 0;

  /// also add
  ///
  ///   bool merge(const T &b, locationt from, locationt to);
  ///    or
  ///   bool merge(const T &b, trace_ptrt from, trace_ptrt to);
  ///
  /// This computes the join between "this" and "b".
  /// Return true if "this" has changed.
  /// In the usual case, "b" is the updated state after "from"
  /// and "this" is the state before "to".
  ///
  /// PRECONDITION(from.is_dereferenceable(), "Must not be _::end()")
  /// PRECONDITION(to.is_dereferenceable(), "Must not be _::end()")

  /// This method allows an expression to be simplified / evaluated using the
  /// current state.  It is used to evaluate assertions and in program
  /// simplification

  /// return true if unchanged
  virtual bool ai_simplify(exprt &condition, const namespacet &) const
  {
    (void)condition; // unused parameter
    return true;
  }

  /// Simplifies the expression but keeps it as an l-value
  virtual bool ai_simplify_lhs(exprt &condition, const namespacet &ns) const;

  /// Gives a Boolean condition that is true for all values represented by the
  /// domain.  This allows domains to be converted into program invariants.
  virtual exprt to_predicate(void) const
  {
    if(is_bottom())
      return false_exprt();
    else
      return true_exprt();
  }
};

// No virtual interface is complete without a factory!
class ai_domain_factory_baset
{
public:
  typedef ai_domain_baset statet;
  typedef ai_domain_baset::locationt locationt;
  typedef ai_domain_baset::trace_ptrt trace_ptrt;

  virtual ~ai_domain_factory_baset()
  {
  }

  virtual std::unique_ptr<statet> make(locationt l) const = 0;
  virtual std::unique_ptr<statet> copy(const statet &s) const = 0;

  // Not domain construction but requires knowing the precise type of statet
  virtual bool
  merge(statet &dest, const statet &src, trace_ptrt from, trace_ptrt to)
    const = 0;
};
// Converting make to take a trace_ptr instead of a location would
// require removing the backwards-compatible
//  location_sensitive_storaget::get_state(locationt l)
// function which is used by some of the older domains

// It would be great to have a single (templated) default implementation.
// However, a default constructor is not part of the ai_domain_baset interface
// and there are some domains which don't have one.  So we need to separate the
// methods.
template <typename domainT>
class ai_domain_factoryt : public ai_domain_factory_baset
{
public:
  typedef ai_domain_factory_baset::statet statet;
  typedef ai_domain_factory_baset::locationt locationt;
  typedef ai_domain_factory_baset::trace_ptrt trace_ptrt;

  std::unique_ptr<statet> copy(const statet &s) const override
  {
    return util_make_unique<domainT>(static_cast<const domainT &>(s));
  }

  bool merge(statet &dest, const statet &src, trace_ptrt from, trace_ptrt to)
    const override
  {
    // For backwards compatability, use the location version
    return static_cast<domainT &>(dest).merge(
      static_cast<const domainT &>(src),
      from->current_location(),
      to->current_location());
  }
};

template <typename domainT>
class ai_domain_factory_default_constructort
  : public ai_domain_factoryt<domainT>
{
public:
  typedef ai_domain_factory_baset::statet statet;
  typedef ai_domain_factory_baset::locationt locationt;
  typedef ai_domain_factory_baset::trace_ptrt trace_ptrt;

  std::unique_ptr<statet> make(locationt l) const override
  {
    auto d = util_make_unique<domainT>();
    CHECK_RETURN(d->is_bottom());
    return std::unique_ptr<statet>(d.release());
  }
};

#endif
