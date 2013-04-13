/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <util/config.h>

#include "cpp_enum_type.h"

cpp_enum_typet::cpp_enum_typet():typet(ID_c_enum)
{
  set(ID_width, config.ansi_c.int_width);
}
