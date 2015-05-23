/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_PARSE_H
#define CPROVER_JAVA_BYTECODE_PARSE_H

#include <string>

#include <util/message.h>

#include "java_bytecode_parse_tree.h"

bool java_bytecode_parse(
  const std::string &file,
  java_bytecode_parse_treet &,
  message_handlert &);

#endif
