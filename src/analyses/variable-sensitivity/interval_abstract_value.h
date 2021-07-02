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

#include <analyses/variable-sensitivity/abstract_value_object.h>

class interval_abstract_valuet : public abstract_value_objectt
{
public:
  explicit interval_abstract_valuet(const typet &t);
  interval_abstract_valuet(const typet &t, bool tp, bool bttm);

  explicit interval_abstract_valuet(const constant_interval_exprt &e);
  interval_abstract_valuet(const exprt &lower, const exprt &upper);

  interval_abstract_valuet(
    const exprt &e,
    const abstract_environmentt &environment,
    const namespacet &ns);

  template <typename... Args>
  static std::shared_ptr<interval_abstract_valuet>
  make_interval(Args &&... args)
  {
    return std::make_shared<interval_abstract_valuet>(
      std::forward<Args>(args)...);
  }

  ~interval_abstract_valuet() override = default;

  index_range_implementation_ptrt
  index_range_implementation(const namespacet &ns) const override;

  value_range_implementation_ptrt value_range_implementation() const override;

  exprt to_constant() const override;
  constant_interval_exprt to_interval() const override
  {
    return interval;
  }

  abstract_value_pointert
  constrain(const exprt &lower, const exprt &upper) const override;

  size_t internal_hash() const override;
  bool internal_equality(const abstract_object_pointert &other) const override;

  void output(
    std::ostream &out,
    const class ai_baset &ai,
    const class namespacet &ns) const override;

  void get_statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) const override;

protected:
  CLONE

  /// Merge another interval abstract object with this one
  /// \param other The abstract value object to merge with
  /// \param widen_mode: Indicates if this is a widening merge
  /// \return This if the other interval is subsumed by this,
  ///          other if this is subsumed by other.
  ///          Otherwise, a new interval abstract object
  ///          with the smallest interval that subsumes both
  ///          this and other
  abstract_object_pointert merge_with_value(
    const abstract_value_pointert &other,
    const widen_modet &widen_mode) const override;

  /// Meet another interval abstract object with this one
  /// \param other The interval abstract object to meet with
  /// \return This if the other interval subsumes this,
  ///          other if this subsumes other.
  ///          Otherwise, a new interval abstract object
  ///          with the intersection interval (of this and other)
  abstract_object_pointert
  meet_with_value(const abstract_value_pointert &other) const override;

private:
  constant_interval_exprt interval;

  void set_top_internal() override;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_INTERVAL_ABSTRACT_VALUE_H
