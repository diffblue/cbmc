/*******************************************************************\

Module: Read Goto Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Read Goto Programs

#ifndef CPROVER_GOTO_PROGRAMS_READ_GOTO_BINARY_H
#define CPROVER_GOTO_PROGRAMS_READ_GOTO_BINARY_H

#include <string>

class goto_functionst;
class goto_modelt;
class message_handlert;
class symbol_tablet;
class concrete_symbol_tablet;

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
  concrete_symbol_tablet &,
  goto_functionst &,
  message_handlert &);

bool read_object_and_link(
  const std::string &file_name,
  goto_modelt &,
  message_handlert &);

#endif // CPROVER_GOTO_PROGRAMS_READ_GOTO_BINARY_H
