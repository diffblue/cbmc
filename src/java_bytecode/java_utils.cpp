/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/prefix.h>
#include <util/std_types.h>

#include "java_utils.h"

bool java_is_array_type(const typet &type)
{
  if(type.id()!=ID_struct)
    return false;
  return has_prefix(id2string(
    to_struct_type(type).get_tag()),
                    "java::array[");
}
