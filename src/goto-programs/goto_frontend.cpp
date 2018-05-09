/*******************************************************************\

Module: API for Language Frontends

Author: Daniel Kroening

\*******************************************************************/

#include "goto_frontend.h"

#include <util/cprover_prefix.h>

goto_frontendt::~goto_frontendt()
{
}

irep_idt goto_frontendt::entry_point() const
{
  // do not confuse with C's "int main()"
  return irep_idt(CPROVER_PREFIX "_start");
}
