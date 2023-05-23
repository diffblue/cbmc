/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_CPROVER_LIBRARY_H
#define CPROVER_ANSI_C_CPROVER_LIBRARY_H

#include <util/symbol_table.h>

#include <set>

class message_handlert;

struct cprover_library_entryt
{
  const char *function;
  const char *model;
};

std::string get_cprover_library_text(
  const std::set<irep_idt> &functions,
  const symbol_table_baset &,
  const struct cprover_library_entryt[],
  const std::string &prologue,
  const bool force_load = false);

/// Parses and typechecks the given src and stores the result in the returned
/// symbol table. Symbols with names found in `keep` will survive
/// the symbol table cleanup pass and be found in the symbol table.
optionalt<symbol_tablet> add_library(
  const std::string &src,
  message_handlert &,
  const std::set<irep_idt> &keep = {});

optionalt<symbol_tablet> cprover_c_library_factory(
  const std::set<irep_idt> &functions,
  const symbol_table_baset &,
  message_handlert &);

/// Load the requested function symbols from the cprover library
/// and return them in the symbol table regardless of
/// the library config flags and usage.
optionalt<symbol_tablet> cprover_c_library_factory_force_load(
  const std::set<irep_idt> &functions,
  const symbol_table_baset &symbol_table,
  message_handlert &message_handler);
#endif // CPROVER_ANSI_C_CPROVER_LIBRARY_H
