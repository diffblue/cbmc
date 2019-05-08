/*******************************************************************\

Module: Element access in a pointer array

Author: Diffblue Ltd.

\*******************************************************************/

#include "array_element_from_pointer.h"

dereference_exprt
array_element_from_pointer(const exprt &pointer, const exprt &index)
{
  PRECONDITION(can_cast_type<pointer_typet>(pointer.type()));
  PRECONDITION(
    index.type().id() == ID_signedbv || index.type().id() == ID_unsignedbv);
  return dereference_exprt{plus_exprt{pointer, index}};
}
