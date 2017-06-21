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
    messaget(_message_handler)
  {
  }

  virtual ~typecheckt() { }

  // not pretty, but makes transition easier
  void err_location(const source_locationt &loc)
  {
    messaget::error().source_location=loc;
  }

  // not pretty, but makes transition easier
  void err_location(const exprt &src)
  {
    err_location(src.find_source_location());
  }

  void err_location(const typet &src)
  {
    err_location(src.source_location());
  }

protected:
  // main function -- overload this one
  virtual void typecheck()=0;

public:
  // call that one
  virtual bool typecheck_main();
};

#endif // CPROVER_UTIL_TYPECHECK_H
