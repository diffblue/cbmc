/*******************************************************************\

 Module: analyses variable-sensitivity variable-sensitivity-value-set

 Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Value sets for primitives

// NOLINTNEXTLINE(whitespace/line_length)
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ABSTRACT_VALUE_H
// NOLINTNEXTLINE(whitespace/line_length)
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ABSTRACT_VALUE_H

#include "abstract_value.h"

class value_set_abstract_valuet : public abstract_valuet
{
public:
  explicit value_set_abstract_valuet(const typet &type);
  CLONE
};

// NOLINTNEXTLINE(whitespace/line_length)
#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ABSTRACT_VALUE_H
