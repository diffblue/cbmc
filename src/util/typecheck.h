/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TYPECHECK_H
#define CPROVER_TYPECHECK_H

#include "message_stream.h"

class typecheckt:public message_streamt
{
public:
  typecheckt(message_handlert &_message_handler):
    message_streamt(_message_handler) { }
  virtual ~typecheckt() { }
  
protected:
  // main function -- overload this one
  virtual void typecheck()=0;

public:
  // call that one
  virtual bool typecheck_main();
};

#endif
