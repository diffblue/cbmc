/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_CPROVER_LIBRARY_H
#define CPROVER_ANSI_C_CPROVER_LIBRARY_H

#include <set>

#include <util/irep.h>

class message_handlert;
class symbol_table_baset;

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

/// Parses and typechecks the given src and adds its contents to the
/// symbol table. Symbols with names found in `keep` will survive
/// the symbol table cleanup pass and be found in the symbol_table.
/// Type-checks the C library model text \p src and links it into the symbol
/// table; \p preprocessed: \p src is already preprocessed (by
/// dump_c_library_models)
void add_library(
  const std::string &src,
  symbol_table_baset &,
  message_handlert &,
  const std::set<irep_idt> &keep = {},
  bool preprocessed = false);

/// Preprocesses each model of the C library with this platform's
/// preprocessor (for the target and options of \ref config) and writes it to
/// \p directory as `FUNCTION.i`, with a manifest, for
/// `--c-library-models` on another host.  Models that differ for a program
/// with C++ code are also written, in that variant, to the subdirectory
/// `cpp-program`.  \return true on error
bool dump_c_library_models(
  const std::string &directory,
  message_handlert &message_handler);

void cprover_c_library_factory(
  const std::set<irep_idt> &functions,
  const symbol_table_baset &,
  symbol_table_baset &,
  message_handlert &);

/// Load the requested function symbols from the cprover library
/// and add them to the symbol table regardless of
/// the library config flags and usage.  \p cpp_program: the models are for
/// a program with C++ code (see \ref has_cpp_code).
void cprover_c_library_factory_force_load(
  const std::set<irep_idt> &functions,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler,
  bool cpp_program = false);

/// Whether \p symbol_table has a symbol of C++ code.  The C library models
/// are then preprocessed with __CPROVER_CPP_PROGRAM defined: only such a
/// program can use new[] and delete[], whose checks need malloc to record
/// its object.
bool has_cpp_code(const symbol_table_baset &symbol_table);

#endif // CPROVER_ANSI_C_CPROVER_LIBRARY_H
