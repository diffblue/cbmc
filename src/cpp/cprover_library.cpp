/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/

#include "cprover_library.h"

#include <sstream>

#include <util/config.h>

#include <ansi-c/cprover_library.h>

static std::string get_cprover_library_text(
  const std::set<irep_idt> &functions,
  const symbol_tablet &symbol_table)
{
  std::ostringstream library_text;

  library_text << "#line 1 \"<builtin-library>\"\n"
               << "#undef inline\n";

  // cprover_library.inc may not have been generated when running Doxygen, thus
  // make Doxygen skip this part
  /// \cond
  const struct cprover_library_entryt cprover_library[] =
#include "cprover_library.inc"
    ; // NOLINT(whitespace/semicolon)
  /// \endcond

  return get_cprover_library_text(
    functions, symbol_table, cprover_library, library_text.str());
}

void cprover_cpp_library_factory(
  const std::set<irep_idt> &functions,
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  if(config.ansi_c.lib == configt::ansi_ct::libt::LIB_NONE)
    return;

  const std::string library_text =
    get_cprover_library_text(functions, symbol_table);

  add_library(library_text, symbol_table, message_handler);
}
