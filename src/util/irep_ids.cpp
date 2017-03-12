/*******************************************************************\

Module: Internal Representation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "irep_ids.h"
#include "string_container.h"

const char *irep_ids_table[]=
{
#define IREP_ID_ONE(id) #id,
#define IREP_ID_TWO(id, str) #str,

#include "irep_ids.def"

  NULL,
};

/*******************************************************************\

Function: initialize_string_container

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void initialize_string_container()
{
  // this is called by the constructor of string_containert

  for(unsigned i=0; irep_ids_table[i]!=NULL; i++)
  {
    unsigned x;
    x=string_container[irep_ids_table[i]];
    assert(x==i); // sanity check
  }
}
