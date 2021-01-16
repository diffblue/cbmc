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
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_INTERVAL_ARRAY_ABSTRACT_OBJECT_H
