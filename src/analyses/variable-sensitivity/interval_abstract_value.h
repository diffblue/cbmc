/*******************************************************************\

 Module: analyses variable-sensitivity intervals

 Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// An interval to represent a set of possible values.

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_INTERVAL_ABSTRACT_VALUE_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_INTERVAL_ABSTRACT_VALUE_H

#include <iosfwd>

#include <util/interval.h>

#include "abstract_object_statistics.h"
#include <analyses/variable-sensitivity/abstract_value_object.h>
#include <util/std_expr.h>

class interval_abstract_valuet : public abstract_value_objectt
{
private:
  typedef sharing_ptrt<interval_abstract_valuet>
    interval_abstract_value_pointert;

public:
  explicit interval_abstract_valuet(const typet &t);
  interval_abstract_valuet(const typet &t, bool tp, bool bttm);

  explicit interval_abstract_valuet(const constant_interval_exprt &e);

  interval_abstract_valuet(
    const exprt &e,
    const abstract_environmentt &environment,
    const namespacet &ns);

  ~interval_abstract_valuet() override = default;

  index_range_ptrt index_range(const namespacet &ns) const override;

  exprt to_constant() const override;

  /// Interface for transforms
  ///
  /// \param expr: the expression to evaluate and find the result of it.
  ///              This will be the symbol referred to be op0()
  /// \param operands: an abstract_object (pointer) that represent
  ///                  the possible values of each operand
  /// \param environment: the abstract environment in which the
  ///                     expression is being evaluated
  /// \param ns: the current variable namespace
  ///
  /// \return Returns the abstract_object representing the result of
  ///         this expression to the maximum precision available.
  ///
  /// Perform the interval transforms
  abstract_object_pointert expression_transform(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const override;

  void output(
    std::ostream &out,
    const class ai_baset &ai,
    const class namespacet &ns) const override;

  const constant_interval_exprt &get_interval() const;

  void get_statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) const override;

protected:
  CLONE
  abstract_object_pointert merge(abstract_object_pointert other) const override;
  abstract_object_pointert
  meet(const abstract_object_pointert &other) const override;

private:
  static abstract_object_pointert evaluate_conditional(
    const exprt &expr,
    const std::vector<interval_abstract_value_pointert> &interval_operands,
    const abstract_environmentt &environment,
    const namespacet &ns);
  static abstract_object_pointert evaluate_unary_expr(
    const exprt &expr,
    const std::vector<interval_abstract_value_pointert> &interval_operands,
    const abstract_environmentt &environment,
    const namespacet &ns);

  abstract_object_pointert
  merge_intervals(interval_abstract_value_pointert other) const;
  abstract_object_pointert
  meet_intervals(interval_abstract_value_pointert other) const;

  constant_interval_exprt interval;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_INTERVAL_ABSTRACT_VALUE_H
