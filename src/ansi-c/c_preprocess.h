/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_C_PREPROCESS_H
#define CPROVER_C_PREPROCESS_H

#include <istream>
#include <ostream>
#include <string>

#include <message.h>

typedef enum { PREPROCESS_AUTO, PREPROCESS_C, PREPROCESS_CPP } preprocess_modet;

bool c_preprocess(
  preprocess_modet mode,
  const std::string &path,
  std::ostream &outstream,
  message_handlert &message_handler);
 
bool c_preprocess(
  preprocess_modet mode,
  std::istream &instream,
  std::ostream &outstream,
  message_handlert &message_handler);
 
#endif
