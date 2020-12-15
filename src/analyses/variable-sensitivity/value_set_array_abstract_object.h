/*******************************************************************\

 Module: analyses variable-sensitivity variable-sensitivity-value-set

 Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Arrays with value sets as indices

// NOLINTNEXTLINE(whitespace/line_length)
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ARRAY_ABSTRACT_OBJECT_H
// NOLINTNEXTLINE(whitespace/line_length)
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ARRAY_ABSTRACT_OBJECT_H

#include "array_abstract_object.h"

class value_set_array_abstract_objectt : public array_abstract_objectt
{
public:
  explicit value_set_array_abstract_objectt(const typet &type);

  abstract_object_pointert write(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const exprt &specifier,
    const abstract_object_pointert &value,
    bool merging_write) const override;

  CLONE
protected:
  abstract_object_pointert write_index(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const index_exprt &index_expr,
    const abstract_object_pointert &value,
    bool merging_write) const override;
};

// NOLINTNEXTLINE(whitespace/line_length)
#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ARRAY_ABSTRACT_OBJECT_H
