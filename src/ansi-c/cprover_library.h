/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_CPROVER_LIBRARY_H
#define CPROVER_ANSI_C_CPROVER_LIBRARY_H

#include <set>

#include <util/symbol_table.h>
#include <util/message.h>

std::string get_cprover_library_text(
  const std::set<irep_idt> &functions,
  const symbol_tablet &);

void add_library(
  const std::string &src,
  symbol_tablet &,
  message_handlert &);

void add_cprover_library(
  const std::set<irep_idt> &functions,
  symbol_tablet &,
  message_handlert &);

#endif // CPROVER_ANSI_C_CPROVER_LIBRARY_H
