/*******************************************************************\

 Module: analyses variable-sensitivity variable-sensitivity-value-set

 Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Pointers pointing to a limited-size set of possible targets

// NOLINTNEXTLINE(whitespace/line_length)
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_POINTER_ABSTRACT_OBJECT_H
// NOLINTNEXTLINE(whitespace/line_length)
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_POINTER_ABSTRACT_OBJECT_H

#include "pointer_abstract_object.h"

class value_set_pointer_abstract_objectt : public pointer_abstract_objectt
{
public:
  explicit value_set_pointer_abstract_objectt(const typet &type);

  abstract_object_pointert merge(abstract_object_pointert other) const override;

  abstract_object_pointert read(
    const abstract_environmentt &env,
    const exprt &specifier,
    const namespacet &ns) const override;

  abstract_object_pointert write(
    abstract_environmentt &environment,
    const namespacet &ns,
    std::stack<exprt> stack,
    const exprt &specifier,
    abstract_object_pointert value,
    bool merging_write) const override;

  CLONE
protected:
  abstract_object_pointert read_dereference(
    const abstract_environmentt &env,
    const namespacet &ns) const override;

  sharing_ptrt<pointer_abstract_objectt> write_dereference(
    abstract_environmentt &environment,
    const namespacet &ns,
    std::stack<exprt> stack,
    abstract_object_pointert value,
    bool merging_write) const override;
};

// NOLINTNEXTLINE(whitespace/line_length)
#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_POINTER_ABSTRACT_OBJECT_H
