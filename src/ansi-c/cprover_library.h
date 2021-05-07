/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_CPROVER_LIBRARY_H
#define CPROVER_ANSI_C_CPROVER_LIBRARY_H

#include <set>

#include <util/irep.h>

class message_handlert;
class symbol_tablet;

struct cprover_library_entryt
{
  const char *function;
  const char *model;
};

std::string get_cprover_library_text(
  const std::set<irep_idt> &functions,
  const symbol_tablet &,
  const struct cprover_library_entryt[],
  const std::string &prologue);

void add_library(
  const std::string &src,
  symbol_tablet &,
  message_handlert &);

void cprover_c_library_factory(
  const std::set<irep_idt> &functions,
  symbol_tablet &,
  message_handlert &);

#endif // CPROVER_ANSI_C_CPROVER_LIBRARY_H
