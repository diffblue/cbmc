/*******************************************************************\

Module: analyses variable-sensitivity interval-values arrays

Author: Diffblue Ltd.

\*******************************************************************/

#include "interval_array_abstract_object.h"
#include "abstract_environment.h"
#include <util/interval.h>

interval_array_abstract_objectt::interval_array_abstract_objectt(typet type)
  : constant_array_abstract_objectt(type)
{
}

interval_array_abstract_objectt::interval_array_abstract_objectt(
  typet type,
  bool top,
  bool bottom)
  : constant_array_abstract_objectt(type, top, bottom)
{
}

interval_array_abstract_objectt::interval_array_abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : constant_array_abstract_objectt(expr, environment, ns)
{
}


