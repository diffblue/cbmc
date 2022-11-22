/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Martin Brain, martin.brain@city.ac.uk

\*******************************************************************/

/// \file
/// This builds on the variable sensitivity domain to track predicates
/// that are true at a given location.
/// It works by tracking expressions that are assumed by branches or
/// assumption instructions and invalidates them when a write changes
/// one or more of the variables.

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_PREDICATE_TRACKING_DOMAIN_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_PREDICATE_TRACKING_DOMAIN_H

#include <analyses/variable-sensitivity/variable_sensitivity_domain.h>

class predicate_tracking_domaint : public variable_sensitivity_domaint
{
public:
  explicit predicate_tracking_domaint(
    variable_sensitivity_object_factory_ptrt _object_factory,
    const vsd_configt &_configuration)
    : variable_sensitivity_domaint(_object_factory, _configuration)
  {
  }

  /// Basic text output of the abstract domain
  ///
  /// \param out: the output stream
  /// \param ai: the abstract interpreter
  /// \param ns: the namespace
  void output(std::ostream &out, const ai_baset &ai, const namespacet &ns)
    const override;

  /// Gives a Boolean expression that is true for all values represented by the
  /// domain.  This allows domains to be converted into program invariants.
  ///
  /// \return exprt describing the domain
  exprt to_predicate() const override;

  exprt to_predicate(const exprt &expr, const namespacet &ns) const;
  exprt to_predicate(const exprt::operandst &exprs, const namespacet &ns) const;

  /// Computes the join between "this" and "b".
  ///
  /// \param b: the other domain
  /// \param from: it's preceding location
  /// \param to: it's current location
  ///
  /// \return true if something has changed.
  virtual bool
  merge(const predicate_tracking_domaint &b, trace_ptrt from, trace_ptrt to);

  // As we are inheriting from VSD we can use this.
  // It's not recommended but clang complains if we unhide this.
  using variable_sensitivity_domaint::merge;

  /// Perform a context aware merge of the changes that have been applied
  /// between function_start and the current state. Anything that has not been
  /// modified will be taken from the \p function_call domain.
  /// \param function_call: The local of the merge - values from here will be
  ///   taken if they have not been modified
  /// \param function_start: The base of the merge - changes that have been made
  ///   between here and the end will be retained.
  /// \param function_end: The end of the merge - changes that have been made
  ///   between the start and here will be retained.
  /// \param ns: The global namespace
  void merge_three_way_function_return(
    const ai_domain_baset &function_call,
    const ai_domain_baset &function_start,
    const ai_domain_baset &function_end,
    const namespacet &ns) override;

  /// Use the information in the domain to simplify the expression
  /// with respect to the current location.  This may be able to
  /// reduce some values to constants.
  ///
  /// \param condition: the expression to simplify
  /// \param ns: the namespace
  ///
  /// \return True if no simplification was made
  bool ai_simplify(exprt &condition, const namespacet &ns) const override;

protected:
  void assume(exprt expr, namespacet ns) override;
  bool assign(
    const exprt &expr,
    const abstract_object_pointert &value,
    const namespacet &ns) override;
};

class predicate_tracking_domain_factoryt
  : public ai_domain_factoryt<predicate_tracking_domaint>
{
public:
  explicit predicate_tracking_domain_factoryt(
    variable_sensitivity_object_factory_ptrt _object_factory,
    const vsd_configt &_configuration)
    : object_factory(_object_factory), configuration(_configuration)
  {
  }

  std::unique_ptr<statet> make(locationt l) const override
  {
    auto d = util_make_unique<predicate_tracking_domaint>(
      object_factory, configuration);
    CHECK_RETURN(d->is_bottom());
    return std::unique_ptr<statet>(d.release());
  }

private:
  variable_sensitivity_object_factory_ptrt object_factory;
  const vsd_configt configuration;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_PREDICATE_TRACKING_DOMAIN_H
