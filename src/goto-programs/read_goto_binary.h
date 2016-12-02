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
  symbol_tablet &,
  goto_functionst &,
  message_handlert &);

bool read_goto_binary(
  const std::string &filename,
  goto_modelt &dest,
  message_handlert &);

bool is_goto_binary(const std::string &filename);

bool read_object_and_link(
  const std::string &file_name,
  symbol_tablet &,
  goto_functionst &,
  message_handlert &);

bool read_object_and_link(
  const std::string &file_name,
  goto_modelt &,
  message_handlert &);

#endif // CPROVER_GOTO_PROGRAMS_READ_GOTO_BINARY_H
