/*******************************************************************\

Module: Write GOTO binaries

Author: CM Wintersteiger

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_WRITE_GOTO_BINARY_H_
#define CPROVER_GOTO_PROGRAMS_WRITE_GOTO_BINARY_H_

#define GOTO_BINARY_VERSION 2

#include <ostream>
#include <string>

class symbol_tablet;
class goto_functionst;
class message_handlert;

bool write_goto_binary(
  std::ostream &out,
  const symbol_tablet &symbol_table,
  const goto_functionst &goto_functions,
  int version=GOTO_BINARY_VERSION);

bool write_goto_binary(
  const std::string &filename,
  const symbol_tablet &lsymbol_table,
  const goto_functionst &goto_functions,
  message_handlert &message_handler);

#endif
