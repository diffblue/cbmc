/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_C_PREPROCESS_H
#define CPROVER_C_PREPROCESS_H

#include <iosfwd>
#include <string>

#include <util/message.h>

bool c_preprocess(
  const std::string &path,
  std::ostream &outstream,
  message_handlert &message_handler);
 
bool c_preprocess(
  std::istream &instream,
  std::ostream &outstream,
  message_handlert &message_handler);

// returns 'true' in case of error
bool test_c_preprocessor(message_handlert &message_handler);
 
#endif
