/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "typecheck.h"

#include "exception_utils.h"
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

  catch(const invalid_source_file_exceptiont &e)
  {
    error().source_location = e.get_source_location();
    error() << e.get_reason() << messaget::eom;
  }

  return message_handler->get_message_count(messaget::M_ERROR)!=errors_before;
}
