/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "cprover_library.h"

#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/message.h>
#include <util/symbol_table_base.h>
#include <util/tempfile.h>
#include <util/unicode.h>

#include "ansi_c_language.h"
#include "c_preprocess.h"

#include <cctype>
#include <filesystem>
#include <fstream>
#include <sstream>

/// The text that precedes the models of the C library: the macros for the
/// options that the models depend on.
static std::string library_prologue()
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

  return library_text.str();
}

// cprover_library.inc may not have been generated when running Doxygen, thus
// make Doxygen skip this part
/// \cond
static const struct cprover_library_entryt cprover_library[] =
#include "cprover_library.inc" // IWYU pragma: keep
  ;                            // NOLINT(whitespace/semicolon)
/// \endcond

static std::string get_cprover_library_text(
  const std::set<irep_idt> &functions,
  const symbol_table_baset &symbol_table,
  const bool force_load)
{
  return get_cprover_library_text(
    functions, symbol_table, cprover_library, library_prologue(), force_load);
}

/// What the models in a directory of preprocessed models were made for: the
/// target and the prologue (the options the models depend on).  Models
/// preprocessed for another target or other options are not used.
static std::string library_models_manifest()
{
  return "os " + configt::ansi_ct::os_to_string(config.ansi_c.os) + "\narch " +
         id2string(config.ansi_c.arch) + "\nmode " +
         std::to_string(static_cast<int>(config.ansi_c.mode)) +
         "\npointer width " + std::to_string(config.ansi_c.pointer_width) +
         "\nprologue\n" + library_prologue();
}

/// The file name of the preprocessed model of \p function: the name with
/// every character other than a letter, a digit, an underscore, a hyphen
/// or a dot written as a percent sign and its two-digit hexadecimal code.
/// Model names may contain characters that file systems or archives do not
/// allow (the Java models' `java::java.io.InputStream.read:()I`).
static std::string model_file_name(const std::string &function)
{
  static const char hex[] = "0123456789ABCDEF";
  std::string result;
  for(const char c : function)
  {
    const unsigned char u = static_cast<unsigned char>(c);
    if(std::isalnum(u) || c == '_' || c == '-' || c == '.')
      result += c;
    else
    {
      result += '%';
      result += hex[u >> 4];
      result += hex[u & 0xf];
    }
  }
  return result + ".i";
}

bool dump_c_library_models(
  const std::string &directory,
  message_handlert &message_handler)
{
  messaget log{message_handler};
  std::error_code error;
  std::filesystem::create_directories(directory, error);
  if(error)
  {
    log.error() << "failed to create directory '" << directory << "'"
                << messaget::eom;
    return true;
  }
  {
    std::ofstream manifest{widen_if_needed(
      (std::filesystem::path{directory} / "manifest").string())};
    manifest << library_models_manifest();
    if(!manifest)
    {
      log.error() << "failed to write the manifest" << messaget::eom;
      return true;
    }
  }
  std::size_t written = 0, failed = 0;
  const std::string prologue = library_prologue();
  for(const cprover_library_entryt *e = cprover_library; e->function != nullptr;
      e++)
  {
    std::istringstream in{prologue + e->model};
    std::ostringstream preprocessed;
    // a model may need headers or definitions this platform lacks; it is
    // then left out, and loading falls back to the built-in model
    null_message_handlert quiet;
    if(c_preprocess(in, preprocessed, quiet))
    {
      ++failed;
      log.debug() << "not preprocessed: " << e->function << messaget::eom;
      continue;
    }
    std::ofstream out{widen_if_needed(
      (std::filesystem::path{directory} / model_file_name(e->function))
        .string())};
    out << preprocessed.str();
    ++written;
  }
  log.status() << "C library models: " << written << " preprocessed, " << failed
               << " not preprocessed, into '" << directory << "'"
               << messaget::eom;
  return false;
}

/// Adds the models of \p functions found in config.ansi_c.c_library_models_dir
/// to \p dest_symbol_table, each as a translation unit of its own (each
/// carries the declarations of the headers it includes), and removes them
/// from \p functions.  Uses no model if the directory's manifest does not
/// match the current target and options.
static void add_preprocessed_library_models(
  std::set<irep_idt> &functions,
  const symbol_table_baset &symbol_table,
  symbol_table_baset &dest_symbol_table,
  message_handlert &message_handler)
{
  messaget log{message_handler};
  const std::string &directory = config.ansi_c.c_library_models_dir;
  std::ifstream manifest_file{
    widen_if_needed((std::filesystem::path{directory} / "manifest").string())};
  std::ostringstream manifest;
  manifest << manifest_file.rdbuf();
  if(!manifest_file || manifest.str() != library_models_manifest())
  {
    // the library is linked in rounds; say it once
    static bool warned = false;
    if(warned)
      return;
    warned = true;
    log.warning() << "the C library models in '" << directory
                  << "' were not preprocessed for this target and these "
                     "options; using the built-in models"
                  << messaget::eom;
    return;
  }
  for(auto it = functions.begin(); it != functions.end();)
  {
    const auto old = symbol_table.symbols.find(*it);
    std::ifstream model{widen_if_needed(
      (std::filesystem::path{directory} / model_file_name(id2string(*it)))
        .string())};
    if(
      old == symbol_table.symbols.end() || old->second.value.is_not_nil() ||
      !model)
    {
      ++it;
      continue;
    }
    std::ostringstream text;
    text << model.rdbuf();
    add_library(text.str(), dest_symbol_table, message_handler, {}, true);
    it = functions.erase(it);
  }
}

/// \p model with every occurrence of the identifier \p from (as a whole
/// word, outside `\#include` lines) replaced by \p to.
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

  std::set<irep_idt> remaining = functions;
  if(!config.ansi_c.c_library_models_dir.empty())
  {
    add_preprocessed_library_models(
      remaining, symbol_table, dest_symbol_table, message_handler);
  }

  std::string library_text =
    get_cprover_library_text(remaining, symbol_table, false);

  add_library(library_text, dest_symbol_table, message_handler);
}

void add_library(
  const std::string &src,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler,
  const std::set<irep_idt> &keep,
  const bool preprocessed)
{
  if(src.empty())
    return;

  std::istringstream in(src);

  ansi_c_languaget ansi_c_language;
  if(preprocessed)
  {
    // a `.i' file is not preprocessed again
    temporary_filet file{"library", ".i"};
    {
      std::ofstream out{widen_if_needed(file())};
      out << src;
    }
    ansi_c_language.parse(in, file(), message_handler);
  }
  else
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
