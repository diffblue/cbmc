/*******************************************************************\

Module: Read Goto Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_READ_GOTO_BINARY_H
#define CPROVER_GOTO_PROGRAMS_READ_GOTO_BINARY_H

#include <string>

class symbol_tablet;
class goto_functionst;
class message_handlert;
class goto_modelt;

bool read_goto_binary(
  const std::string &filename,
  symbol_tablet &symbol_table,
  goto_functionst &dest,
  message_handlert &message_handler);
  
bool read_goto_binary(
  const std::string &filename,
  goto_modelt &dest,
  message_handlert &message_handler);
  
bool is_goto_binary(const std::string &filename);

#endif
