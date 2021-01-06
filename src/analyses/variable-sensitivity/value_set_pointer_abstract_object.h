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

  CLONE
};

// NOLINTNEXTLINE(whitespace/line_length)
#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_POINTER_ABSTRACT_OBJECT_H
