/*******************************************************************\

Module: Read Goto Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_READ_GOTO_BINARY_H
#define CPROVER_GOTO_PROGRAMS_READ_GOTO_BINARY_H

#include <string>

class contextt;
class goto_functionst;
class message_handlert;

bool read_goto_binary(
  const std::string &filename,
  contextt &context,
  goto_functionst &dest,
  message_handlert &message_handler);
  
bool is_goto_binary(const std::string &filename);

#endif
