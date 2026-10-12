/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "cprover_library.h"

#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>
#include <util/std_types.h>
#include <util/symbol_table_base.h>

#include "ansi_c_language.h"

#include <algorithm>
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

  library_text << "#line 1 \"<builtin-library>\"\n"
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

/// Copy the string or character literal starting at \p line[\p pos] (an
/// opening quote) to \p result.
/// \return The position after the closing quote (or the end of \p line).
static std::size_t
copy_literal(const std::string &line, std::size_t pos, std::string &result)
{
  const char quote = line[pos];
  std::size_t end = pos + 1;
  while(end < line.size() && line[end] != quote)
    end += line[end] == '\\' ? 2 : 1;
  end = std::min(end + 1, line.size());
  result.append(line, pos, end - pos);
  return end;
}

std::string rename_in_model(
  const std::string &model,
  const std::string &from,
  const std::string &to)
{
  PRECONDITION(!from.empty());
  const auto is_word = [](char c)
  { return std::isalnum(static_cast<unsigned char>(c)) || c == '_'; };
  std::istringstream in(model);
  std::ostringstream out;
  std::string line;
  while(std::getline(in, line))
  {
    std::size_t first = line.find_first_not_of(" \t");
    if(first != std::string::npos && line[first] == '#')
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
    while(pos < line.size())
    {
      if(line[pos] == '"' || line[pos] == '\'')
      {
        pos = copy_literal(line, pos, result);
        continue;
      }
      const std::size_t end = pos + from.size();
      if(
        line.compare(pos, from.size(), from) == 0 &&
        (pos == 0 || !is_word(line[pos - 1])) &&
        (end >= line.size() || !is_word(line[end])))
      {
        result += to;
        pos = end;
      }
      else
        result += line[pos++];
    }
    out << result << '\n';
  }
  return out.str();
}

/// True if \p type is a va_list (`__builtin_va_list`, which is a struct on
/// aarch64 and a pointer elsewhere).
static bool is_va_list(const typet &type)
{
  const irep_idt &typedef_name = type.get(ID_C_typedef);
  return typedef_name == "__builtin_va_list" || typedef_name == "va_list" ||
         typedef_name == "__gnuc_va_list" ||
         (type.id() == ID_struct_tag &&
          to_struct_tag_type(type).get_identifier() == "tag-__va_list");
}

/// GCC and Clang provide `__builtin_X` for many C library functions X, with
/// X's meaning (GCC manual, "Other Built-in Functions Provided by GCC";
/// libc++'s <cmath> calls __builtin_ceil, __builtin_sqrt, ...). Pick the model
/// of X for \p builtin when \p builtin has no model of its own and X's model
/// is compatible with \p declaration of \p builtin.
/// \param builtin: name of the function to find a model for
/// \param declaration: symbol of \p builtin, nullptr if there is none
/// \param cprover_library: the available models
/// \return The model of X, or nullptr if there is none or it must not be used.
static const cprover_library_entryt *builtin_fallback_model(
  const irep_idt &builtin,
  const symbolt *declaration,
  const cprover_library_entryt cprover_library[])
{
  const std::string &name = id2string(builtin);
  const std::string prefix = "__builtin_";
  if(!has_prefix(name, prefix) || name.size() == prefix.size())
    return nullptr;
  const std::string plain = name.substr(prefix.size());

  // Builtins whose declaration and model of X are incompatible: GCC's
  // __builtin_setjmp and __builtin_longjmp are not the C library's setjmp and
  // longjmp (they take a five-word buffer, and the value must be 1); the
  // declarations of the stream functions take void * rather than FILE *
  // streams (linking would warn that pointer parameter types differ).
  static const std::set<std::string> excluded = {
    "__fprintf_chk",
    "fprintf",
    "fputs",
    "fscanf",
    "fwrite",
    "longjmp",
    "setjmp"};
  if(excluded.find(plain) != excluded.end())
    return nullptr;

  // We need the declaration to check that X's model fits.
  if(declaration == nullptr || declaration->type.id() != ID_code)
    return nullptr;
  const code_typet &type = to_code_type(declaration->type);
  // A declaration without a prototype is type-generic (__builtin_isfinite,
  // ...), while X's model fixes the parameter types.
  if(type.parameters().empty() && type.has_ellipsis())
    return nullptr;
  // Where va_list is a struct (aarch64), a va_list parameter of the C++
  // declaration of __builtin_X and that of the C model of X have different
  // types, and linking leaves the model's va_list typedef dangling
  // (--validate-goto-model: "va_list not found").
  for(const auto &parameter : type.parameters())
  {
    if(is_va_list(parameter.type()))
      return nullptr;
  }

  const cprover_library_entryt *of_plain = nullptr;
  for(const cprover_library_entryt *e = cprover_library; e->function != nullptr;
      e++)
  {
    if(name == e->function)
      return nullptr; // a model of its own is used instead
    if(of_plain == nullptr && plain == e->function)
      of_plain = e;
  }
  return of_plain;
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

  std::size_t count = 0;

  for(const cprover_library_entryt *e = cprover_library; e->function != nullptr;
      e++)
  {
    irep_idt id = e->function;

    if(functions.find(id) != functions.end())
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

  // Without a model of its own, `__builtin_X' gets X's model under its own
  // name (see builtin_fallback_model).
  for(const auto &id : functions)
  {
    const auto old = symbol_table.symbols.find(id);
    const symbolt *declaration =
      old == symbol_table.symbols.end() ? nullptr : &old->second;
    const cprover_library_entryt *model =
      builtin_fallback_model(id, declaration, cprover_library);
    if(model != nullptr && (force_load || declaration->value.is_nil()))
    {
      count++;
      library_text << rename_in_model(
                        model->model, model->function, id2string(id))
                   << '\n';
    }
  }

  if(count == 0)
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
  if(config.ansi_c.lib == configt::ansi_ct::libt::LIB_NONE)
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
