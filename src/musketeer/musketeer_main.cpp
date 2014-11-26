/*******************************************************************\

Module: Main Module 

Author: Vincent Nimal

\*******************************************************************/

#include "musketeer_parseoptions.h"

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int main(int argc, const char **argv)
{
  goto_fence_inserter_parseoptionst parseoptions(argc, argv);
  return parseoptions.main();
}
