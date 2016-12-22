/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_TYPECHECK_H
#define CPROVER_UTIL_TYPECHECK_H

#include "message_stream.h"

class legacy_typecheckt:public legacy_message_streamt
{
public:
  explicit legacy_typecheckt(message_handlert &_message_handler):
    legacy_message_streamt(_message_handler) { }
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

  // not pretty, but makes transition easier
  inline void err_location(const exprt &src)
  {
    error().source_location=src.find_source_location();
  }

  bool error_found;

  inline bool get_error_found() const
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
