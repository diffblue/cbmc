/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

/// \file
/// An abstraction of a single value that just stores a constant.

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_ABSTRACT_VALUE_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_ABSTRACT_VALUE_H

#include <iosfwd>

#include <analyses/variable-sensitivity/abstract_value_object.h>
#include <util/std_expr.h>

class constant_abstract_valuet : public abstract_value_objectt
{
private:
  typedef sharing_ptrt<constant_abstract_valuet>
    constant_abstract_value_pointert;

public:
  explicit constant_abstract_valuet(const typet &t);
  constant_abstract_valuet(const typet &t, bool tp, bool bttm);
  constant_abstract_valuet(
    const exprt &e,
    const abstract_environmentt &environment,
    const namespacet &ns);

  ~constant_abstract_valuet() override = default;

  index_range_ptrt index_range(const namespacet &ns) const override;

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
  /// Uses the rewriter to constant fold expressions where possible.
  abstract_object_pointert expression_transform(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const override;

  exprt to_constant() const override;

  void output(
    std::ostream &out,
    const class ai_baset &ai,
    const class namespacet &ns) const override;

  void get_statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) const override;

  size_t internal_hash() const override
  {
    return std::hash<std::string>{}(value.pretty());
  }

  bool internal_equality(const abstract_object_pointert &other) const override
  {
    auto cast_other =
      std::dynamic_pointer_cast<const constant_abstract_valuet>(other);
    return cast_other && value == cast_other->value;
  }

protected:
  CLONE

  /// Attempts to do a constant/constant merge if both are constants,
  /// otherwise falls back to the parent merge
  ///
  /// \param other: the abstract object to merge with
  ///
  /// \return Returns the result of the merge
  abstract_object_pointert merge(abstract_object_pointert other) const override;

  abstract_object_pointert try_transform_expr_with_all_rounding_modes(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns) const;

private:
  /// Merges another constant abstract value into this one
  ///
  /// \param other: the abstract object to merge with
  ///
  /// \return Returns a new abstract object that is the result of the merge
  ///         unless the merge is the same as this abstract object, in which
  ///         case it returns this.
  abstract_object_pointert
  merge_constant_constant(const constant_abstract_value_pointert &other) const;

  exprt value;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_ABSTRACT_VALUE_H
