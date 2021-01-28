
/*******************************************************************\

 Module: analyses variable-sensitivity variable-sensitivity-value-set

 Author: Diffblue Ltd.

\*******************************************************************/

#include "value_set_pointer_abstract_object.h"

abstract_object_pointert
value_set_pointer_abstract_objectt::merge(abstract_object_pointert other) const
{
  return shared_from_this();
}

value_set_pointer_abstract_objectt::value_set_pointer_abstract_objectt(
  const typet &type)
  : pointer_abstract_objectt(type)
{
}

