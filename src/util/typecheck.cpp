/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "typecheck.h"

#include "invariant.h"

bool typecheckt::typecheck_main()
{
  PRECONDITION(message_handler);

  const unsigned errors_before=
    message_handler->get_message_count(messaget::M_ERROR);

  try
  {
    typecheck();
  }

  catch(int)
  {
    error();
  }

  catch(const char *e)
  {
    error() << e << eom;
  }

  catch(const std::string &e)
  {
    error() << e << eom;
  }

  return message_handler->get_message_count(messaget::M_ERROR)!=errors_before;
}
