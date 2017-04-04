/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_TYPECHECK_H
#define CPROVER_UTIL_TYPECHECK_H

#include "expr.h"
#include "message.h"

class typecheckt:public messaget
{
public:
  explicit typecheckt(message_handlert &_message_handler):
    messaget(_message_handler),
    error_found(false)
  {
  }

  virtual ~typecheckt() { }

  mstreamt &error()
  {
    error_found=true;
    return messaget::error();
  }

  // not pretty, but makes transition easier
  void err_location(const exprt &src)
  {
    error().source_location=src.find_source_location();
  }

  bool error_found;

  bool get_error_found() const
  {
    return error_found;
  }

protected:
  // main function -- overload this one
  virtual void typecheck()=0;

public:
  // call that one
  virtual bool typecheck_main();
};

#endif // CPROVER_UTIL_TYPECHECK_H
