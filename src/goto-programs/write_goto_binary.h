/*******************************************************************\

Module: Write GOTO binaries

Author: CM Wintersteiger

\*******************************************************************/

/// \file
/// Write GOTO binaries

#ifndef CPROVER_GOTO_PROGRAMS_WRITE_GOTO_BINARY_H
#define CPROVER_GOTO_PROGRAMS_WRITE_GOTO_BINARY_H

#define GOTO_BINARY_VERSION 4

#include <iosfwd>
#include <string>

#include "goto_functions.h"

class goto_modelt;
class message_handlert;

bool write_goto_binary(
  std::ostream &out,
  const goto_modelt &,
  int version=GOTO_BINARY_VERSION);

bool write_goto_binary(
  std::ostream &out,
  const symbol_tablet &,
  const goto_functionst &,
  int version=GOTO_BINARY_VERSION);

bool write_goto_binary(
  const std::string &filename,
  const goto_modelt &,
  message_handlert &);

#endif // CPROVER_GOTO_PROGRAMS_WRITE_GOTO_BINARY_H
