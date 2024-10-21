/*******************************************************************\

Module: Read goto object files.

Author: CM Wintersteiger

Date: May 2007

\*******************************************************************/

/// \file
/// Read goto object files.

#ifndef CPROVER_GOTO_PROGRAMS_READ_BIN_GOTO_OBJECT_H
#define CPROVER_GOTO_PROGRAMS_READ_BIN_GOTO_OBJECT_H

#include <util/nodiscard.h>

#include <iosfwd>
#include <string>

class symbol_table_baset;
class goto_functionst;
class message_handlert;

NODISCARD
bool read_bin_goto_object(
  std::istream &in,
  const std::string &filename,
  symbol_table_baset &symbol_table,
  goto_functionst &goto_functions,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_PROGRAMS_READ_BIN_GOTO_OBJECT_H
