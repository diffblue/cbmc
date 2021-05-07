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

  interval_abstract_valuet(
    const exprt &e,
    const abstract_environmentt &environment,
    const namespacet &ns);

  ~interval_abstract_valuet() override = default;

  index_range_implementation_ptrt
  index_range_implementation(const namespacet &ns) const override;

  value_range_implementation_ptrt value_range_implementation() const override;

  exprt to_constant() const override;
  constant_interval_exprt to_interval() const override
  {
    return interval;
  }

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
  abstract_object_pointert merge(abstract_object_pointert other) const override;
  abstract_object_pointert
  meet(const abstract_object_pointert &other) const override;

private:
  using interval_abstract_value_pointert =
    sharing_ptrt<interval_abstract_valuet>;

  abstract_object_pointert
  merge_intervals(abstract_value_pointert &other) const;
  abstract_object_pointert
  meet_intervals(interval_abstract_value_pointert other) const;

  constant_interval_exprt interval;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_INTERVAL_ABSTRACT_VALUE_H
