/*******************************************************************\

Module: Abstract Interpretation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstract Interpretation Domain

#ifndef CPROVER_ANALYSES_AI_DOMAIN_H
#define CPROVER_ANALYSES_AI_DOMAIN_H

#include <util/expr.h>
#include <util/json.h>
#include <util/make_unique.h>
#include <util/xml.h>

#include <goto-programs/goto_model.h>

// forward reference the abstract interpreter interface
class ai_baset;

/// The interface offered by a domain, allows code to manipulate domains without
/// knowing their exact type.  Derive from this to implement domains.
class ai_domain_baset
{
protected:
  /// The constructor is expected to produce 'false' or 'bottom'
  ai_domain_baset()
  {
  }

public:
  virtual ~ai_domain_baset()
  {
  }

  typedef goto_programt::const_targett locationt;

  /// how function calls are treated:
  /// a) there is an edge from each call site to the function head
  /// b) there is an edge from the last instruction (END_FUNCTION)
  ///    of the function to the instruction _following_ the call site
  ///    (this also needs to set the LHS, if applicable)
  ///
  /// "this" is the domain before the instruction "from"
  /// "from" is the instruction to be interpreted
  /// "to" is the next instruction (for GOTO, FUNCTION_CALL, END_FUNCTION)
  ///
  /// PRECONDITION(from.is_dereferenceable(), "Must not be _::end()")
  /// PRECONDITION(to.is_dereferenceable(), "Must not be _::end()")
  /// PRECONDITION(are_comparable(from,to) ||
  ///              (from->is_function_call() || from->is_end_function())

  virtual void transform(
    const irep_idt &function_from,
    locationt from,
    const irep_idt &function_to,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) = 0;

  virtual void
  output(std::ostream &out, const ai_baset &ai, const namespacet &ns) const
  {
  }

  virtual jsont output_json(const ai_baset &ai, const namespacet &ns) const;

  virtual xmlt output_xml(const ai_baset &ai, const namespacet &ns) const;

  /// no states
  virtual void make_bottom() = 0;

  /// all states -- the analysis doesn't use this,
  /// and domains may refuse to implement it.
  virtual void make_top() = 0;

  /// a reasonable entry-point state
  virtual void make_entry() = 0;

  virtual bool is_bottom() const = 0;

  virtual bool is_top() const = 0;

  /// also add
  ///
  ///   bool merge(const T &b, locationt from, locationt to);
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
  virtual bool ai_simplify(exprt &condition, const namespacet &ns) const
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

#endif
