/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "cprover_library.h"

#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/symbol_table_base.h>

#include "ansi_c_language.h"

#include <cctype>
#include <sstream>

static std::string get_cprover_library_text(
  const std::set<irep_idt> &functions,
  const symbol_table_baset &symbol_table,
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

  if(config.ansi_c.dfcc_debug_lib)
    library_text << "#define " CPROVER_PREFIX "DFCC_DEBUG_LIB\n";

  if(config.ansi_c.simple_invalid_pointer_model)
    library_text << "#define " CPROVER_PREFIX
                    "DFCC_SIMPLE_INVALID_POINTER_MODEL\n";

  // cprover_library.inc may not have been generated when running Doxygen, thus
  // make Doxygen skip this part
  /// \cond
  const struct cprover_library_entryt cprover_library[] =
#include "cprover_library.inc" // IWYU pragma: keep
    ;                          // NOLINT(whitespace/semicolon)
  /// \endcond

  return get_cprover_library_text(
    functions, symbol_table, cprover_library, library_text.str(), force_load);
}

/// \p model with every occurrence of the identifier \p from (as a whole
/// word, outside `\#include' lines) replaced by \p to.
static std::string rename_in_model(
  const std::string &model,
  const std::string &from,
  const std::string &to)
{
  const auto is_word = [](char c)
  { return std::isalnum(static_cast<unsigned char>(c)) || c == '_'; };
  std::istringstream in(model);
  std::ostringstream out;
  std::string line;
  while(std::getline(in, line))
  {
    std::size_t first = line.find_first_not_of(" \t");
    if(first != std::string::npos && line.compare(first, 1, "#") == 0)
    {
      std::size_t directive = line.find_first_not_of(" \t", first + 1);
      if(
        directive != std::string::npos &&
        line.compare(directive, 7, "include") == 0)
      {
        out << line << '\n';
        continue;
      }
    }
    std::string result;
    std::size_t pos = 0;
    while(true)
    {
      const std::size_t hit = line.find(from, pos);
      if(hit == std::string::npos)
      {
        result.append(line, pos, std::string::npos);
        break;
      }
      const std::size_t end = hit + from.size();
      const bool whole = (hit == 0 || !is_word(line[hit - 1])) &&
                         (end == line.size() || !is_word(line[end]));
      result.append(line, pos, hit - pos);
      result += whole ? to : from;
      pos = end;
    }
    out << result << '\n';
  }
  return out.str();
}

std::string get_cprover_library_text(
  const std::set<irep_idt> &functions,
  const symbol_table_baset &symbol_table,
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
      symbol_table_baset::symbolst::const_iterator old =
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

  // GCC and Clang provide `__builtin_X' for each C library function X, with
  // X's meaning (GCC manual, "Other Built-in Functions Provided by GCC";
  // libc++'s <cmath> calls __builtin_ceil, __builtin_sqrt, ...).  Without a
  // model of its own, `__builtin_X' gets X's model under its own name.
  for(const auto &id : functions)
  {
    const std::string name = id2string(id);
    const std::string prefix = "__builtin_";
    if(name.compare(0, prefix.size(), prefix) != 0)
      continue;
    const std::string plain = name.substr(prefix.size());
    if(plain.empty())
      continue;
    const cprover_library_entryt *own = nullptr;
    const cprover_library_entryt *of_plain = nullptr;
    for(const cprover_library_entryt *e = cprover_library;
        e->function != nullptr;
        e++)
    {
      if(name == e->function)
        own = e;
      else if(plain == e->function)
        of_plain = e;
    }
    // A model taking a va_list (vsnprintf, ...) is not reused: where
    // va_list is a struct (aarch64), the C++ declaration of __builtin_X and
    // the C model then have different parameter types, and linking left
    // the model's va_list typedef dangling (--validate-goto-model:
    // "va_list not found").
    if(
      own != nullptr || of_plain == nullptr ||
      std::string{of_plain->model}.find("va_list") != std::string::npos)
    {
      continue;
    }
    const auto old = symbol_table.symbols.find(id);
    if(
      force_load ||
      (old != symbol_table.symbols.end() && old->second.value.is_nil()))
    {
      count++;
      library_text << rename_in_model(of_plain->model, plain, name) << '\n';
    }
  }

  if(count==0)
    return std::string();
  else
    return library_text.str();
}

void cprover_c_library_factory(
  const std::set<irep_idt> &functions,
  const symbol_table_baset &symbol_table,
  symbol_table_baset &dest_symbol_table,
  message_handlert &message_handler)
{
  if(config.ansi_c.lib==configt::ansi_ct::libt::LIB_NONE)
    return;

  std::string library_text =
    get_cprover_library_text(functions, symbol_table, false);

  add_library(library_text, dest_symbol_table, message_handler);
}

void add_library(
  const std::string &src,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler,
  const std::set<irep_idt> &keep)
{
  if(src.empty())
    return;

  std::istringstream in(src);

  ansi_c_languaget ansi_c_language;
  ansi_c_language.parse(in, "", message_handler);

  ansi_c_language.typecheck(
    symbol_table, "<built-in-library>", message_handler, true, keep);
}

void cprover_c_library_factory_force_load(
  const std::set<irep_idt> &functions,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  std::string library_text =
    get_cprover_library_text(functions, symbol_table, true);
  add_library(library_text, symbol_table, message_handler, functions);
}
