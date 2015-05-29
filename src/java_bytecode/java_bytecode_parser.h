/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_PARSE_H
#define CPROVER_JAVA_BYTECODE_PARSE_H

#include <string>

bool java_bytecode_parse(
  const std::string &file,
  class java_bytecode_parse_treet &,
  class message_handlert &);

#endif
