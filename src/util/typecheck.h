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

protected:
  // main function -- overload this one
  virtual void typecheck()=0;

public:
  // call that one
  virtual bool typecheck_main();
};

#endif // CPROVER_UTIL_TYPECHECK_H
