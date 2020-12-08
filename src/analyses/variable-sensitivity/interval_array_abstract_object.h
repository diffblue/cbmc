/*******************************************************************\

Module: analyses variable-sensitivity interval-values arrays

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// An abstraction of an array using intervals
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_INTERVAL_ARRAY_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_INTERVAL_ARRAY_ABSTRACT_OBJECT_H

#include "constant_array_abstract_object.h"

class interval_array_abstract_objectt : public constant_array_abstract_objectt
{
public:
  explicit interval_array_abstract_objectt(typet type);

  interval_array_abstract_objectt(typet type, bool top, bool bottom);

  interval_array_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

protected:
  CLONE
  abstract_object_pointert read_index(
    const abstract_environmentt &env,
    const index_exprt &index,
    const namespacet &ns) const override;

  abstract_object_pointert write_index(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const index_exprt &index_expr,
    const abstract_object_pointert &value,
    bool merging_write) const override;

  bool eval_index(
    const index_exprt &index,
    const abstract_environmentt &env,
    const namespacet &ns,
    mp_integer &out_index) const override;

public:
  void get_statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) const override;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_INTERVAL_ARRAY_ABSTRACT_OBJECT_H
