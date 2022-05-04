/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "cprover_library.h"

#include <sstream>

#include <util/config.h>
#include <util/symbol_table.h>

#include "ansi_c_language.h"

static std::string get_cprover_library_text(
  const std::set<irep_idt> &functions,
  const symbol_tablet &symbol_table,
  const bool force_load)
{
  std::ostringstream library_text;

  library_text << "#line 1 \"<built-in-additions>\"\n"
                  "#define " CPROVER_PREFIX "malloc_failure_mode "
               << std::to_string(config.ansi_c.malloc_failure_mode)
               << "\n"
                  "#define " CPROVER_PREFIX "malloc_failure_mode_return_null "
               << std::to_string(config.ansi_c.malloc_failure_mode_return_null)
               << "\n"
                  "#define " CPROVER_PREFIX
                  "malloc_failure_mode_assert_then_assume "
               << std::to_string(
                    config.ansi_c.malloc_failure_mode_assert_then_assume)
               << "\n"
                  "#define " CPROVER_PREFIX "malloc_may_fail "
               << std::to_string(config.ansi_c.malloc_may_fail) << "\n";

  library_text <<
    "#line 1 \"<builtin-library>\"\n"
    "#undef inline\n";

  if(config.ansi_c.string_abstraction)
    library_text << "#define " CPROVER_PREFIX "STRING_ABSTRACTION\n";

  // cprover_library.inc may not have been generated when running Doxygen, thus
  // make Doxygen skip this part
  /// \cond
  const struct cprover_library_entryt cprover_library[] =
#include "cprover_library.inc"
    ; // NOLINT(whitespace/semicolon)
  /// \endcond

  return get_cprover_library_text(
    functions, symbol_table, cprover_library, library_text.str(), force_load);
}

std::string get_cprover_library_text(
  const std::set<irep_idt> &functions,
  const symbol_tablet &symbol_table,
  const struct cprover_library_entryt cprover_library[],
  const std::string &prologue,
  const bool force_load)
{
  // the default mode is ios_base::out which means subsequent write to the
  // stream will overwrite the original content
  std::ostringstream library_text(prologue, std::ios_base::ate);

  std::size_t count=0;

  for(const cprover_library_entryt *e = cprover_library; e->function != nullptr;
      e++)
  {
    irep_idt id=e->function;

    if(functions.find(id)!=functions.end())
    {
      symbol_tablet::symbolst::const_iterator old=
        symbol_table.symbols.find(id);

      if(
        force_load ||
        (old != symbol_table.symbols.end() && old->second.value.is_nil()))
      {
        count++;
        library_text << e->model << '\n';
      }
    }
  }

  if(count==0)
    return std::string();
  else
    return library_text.str();
}

void cprover_c_library_factory(
  const std::set<irep_idt> &functions,
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  if(config.ansi_c.lib==configt::ansi_ct::libt::LIB_NONE)
    return;

  std::string library_text =
    get_cprover_library_text(functions, symbol_table, false);

  add_library(library_text, symbol_table, message_handler);
}

void add_library(
  const std::string &src,
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  const std::set<irep_idt> &keep)
{
  if(src.empty())
    return;

  std::istringstream in(src);

  ansi_c_languaget ansi_c_language;
  ansi_c_language.set_message_handler(message_handler);
  ansi_c_language.parse(in, "");

  ansi_c_language.typecheck(symbol_table, "<built-in-library>", true, keep);
}

void cprover_c_library_factory_force_load(
  const std::set<irep_idt> &functions,
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  std::string library_text =
    get_cprover_library_text(functions, symbol_table, true);
  add_library(library_text, symbol_table, message_handler, functions);
}
