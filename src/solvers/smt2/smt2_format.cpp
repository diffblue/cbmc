/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2_format.h"

#include <util/std_types.h>

std::ostream &operator<<(std::ostream &out, const smt2_format &f)
{
  if(f.type.id() == ID_unsignedbv)
    out << "(_ BitVec " << to_unsignedbv_type(f.type).get_width() << ')';
  else if(f.type.id() == ID_bool)
    out << "Bool";
  else if(f.type.id() == ID_integer)
    out << "Int";
  else if(f.type.id() == ID_real)
    out << "Real";
  else
    out << "? " << f.type.id();

  return out;
}
