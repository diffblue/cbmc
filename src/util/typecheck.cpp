/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "typecheck.h"

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool typecheckt::typecheck_main()
{
  try
  {
    typecheck();
  }

  catch(int e)
  {
    error();
  }

  catch(const char *e)
  {
    error(e);
  }

  catch(const std::string &e)
  {
    error(e);
  }

  return error_found;
}
