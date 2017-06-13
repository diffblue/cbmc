/*******************************************************************\

Module: Preprocessing Base Class

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Preprocessing Base Class

#ifndef CPROVER_UTIL_PREPROCESSOR_H
#define CPROVER_UTIL_PREPROCESSOR_H

#include <iosfwd>
#include <string>

#include "message.h"

class preprocessort:public messaget
{
public:
  preprocessort(
    std::istream &_in,
    std::ostream &_out,
    message_handlert &_message_handler,
    const std::string &_filename):
    messaget(_message_handler),
    in(_in), out(_out),
    filename(_filename)
  {
  }

  virtual ~preprocessort() { }

  std::istream &in;
  std::ostream &out;
  std::string filename;

  virtual void preprocessor()=0;
};

#endif // CPROVER_UTIL_PREPROCESSOR_H
