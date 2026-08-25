/*******************************************************************\

Module: Write GOTO binaries

Author: CM Wintersteiger

\*******************************************************************/

/// \file
/// Write GOTO binaries

#ifndef CPROVER_GOTO_PROGRAMS_WRITE_GOTO_BINARY_H
#define CPROVER_GOTO_PROGRAMS_WRITE_GOTO_BINARY_H

#define GOTO_BINARY_VERSION 6

#include <iosfwd>
#include <string>

class goto_functionst;
class goto_modelt;
class message_handlert;
class symbol_table_baset;

[[nodiscard]] bool write_goto_binary(
  std::ostream &out,
  const goto_modelt &,
  message_handlert &,
  int version = GOTO_BINARY_VERSION);

[[nodiscard]] bool write_goto_binary(
  std::ostream &out,
  const symbol_table_baset &,
  const goto_functionst &,
  message_handlert &,
  int version = GOTO_BINARY_VERSION);

[[nodiscard]] bool write_goto_binary(
  const std::string &filename,
  const goto_modelt &,
  message_handlert &);

#endif // CPROVER_GOTO_PROGRAMS_WRITE_GOTO_BINARY_H
