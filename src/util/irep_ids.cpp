/*******************************************************************\

Module: Internal Representation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include "irep_ids.h"
#include "string_container.h"

const char *irep_ids_table[]={
  #include "irep_ids.inc"
  NULL
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
