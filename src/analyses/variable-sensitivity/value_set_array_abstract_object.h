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

  CLONE
};

// NOLINTNEXTLINE(whitespace/line_length)
#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ARRAY_ABSTRACT_OBJECT_H
