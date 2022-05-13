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
  const std::string &prologue,
  const bool force_load = false);

/// Parses and typechecks the given src and adds its contents to the
/// symbol table. Symbols with names found in `keep` will survive
/// the symbol table cleanup pass and be found in the symbol_table.
void add_library(
  const std::string &src,
  symbol_tablet &,
  message_handlert &,
  const std::set<irep_idt> &keep = {});

void cprover_c_library_factory(
  const std::set<irep_idt> &functions,
  symbol_tablet &,
  message_handlert &);

/// Load the requested function symbols from the cprover library
/// and add them to the symbol table regardless of
/// the library config flags and usage.
void cprover_c_library_factory_force_load(
  const std::set<irep_idt> &functions,
  symbol_tablet &symbol_table,
  message_handlert &message_handler);
#endif // CPROVER_ANSI_C_CPROVER_LIBRARY_H
