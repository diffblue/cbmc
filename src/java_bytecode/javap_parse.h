/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVAP_PARSE_H
#define CPROVER_JAVAP_PARSE_H

#include <string>

#include <message.h>

#include "java_bytecode_parse_tree.h"

bool javap_parse(
  const std::string &file,
  java_bytecode_parse_treet &,
  message_handlert &);

#endif
