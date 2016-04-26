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

bool legacy_typecheckt::typecheck_main()
{
  try
  {
    typecheck();
  }

  catch(int)
  {
    error_msg();
  }

  catch(const char *e)
  {
    str << e;
    error_msg();
  }

  catch(const std::string &e)
  {
    str << e;
    error_msg();
  }

  return error_found;
}

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

  catch(int)
  {
    error_found=true;
  }

  catch(const char *e)
  {
    error() << e << eom;
  }

  catch(const std::string &e)
  {
    error() << e << eom;
  }

  return error_found;
}
