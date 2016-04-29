/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TYPECHECK_H
#define CPROVER_TYPECHECK_H

#include "message_stream.h"

class legacy_typecheckt:public message_streamt
{
public:
  legacy_typecheckt(message_handlert &_message_handler):
    message_streamt(_message_handler) { }
  virtual ~legacy_typecheckt() { }
  
protected:
  // main function -- overload this one
  virtual void typecheck()=0;

public:
  // call that one
  virtual bool typecheck_main();
};

class typecheckt:public messaget
{
public:
  explicit typecheckt(message_handlert &_message_handler):
    messaget(_message_handler),
    error_found(false)
  {
  }

  virtual ~typecheckt() { }

  inline mstreamt &error()
  {
    error_found=true;
    return messaget::error();
  }

  bool error_found;

protected:
  // main function -- overload this one
  virtual void typecheck()=0;

public:
  // call that one
  virtual bool typecheck_main();
};

#endif
