/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include "mode.h"

#include <list>
#include <memory>
#include <set>

#ifdef _WIN32
#include <cstring>
#endif

#include "language.h"
#include "language_info.h"

#include <util/invariant.h>
#include <util/namespace.h>

typedef std::list<std::unique_ptr<language_infot>> languagest;
languagest languages;

/// Register a language
/// Note: registering a language is required for using the functions
///   in language_util.h
/// \param factory: a language info factory, e.g. `new_ansi_c_language_info`
void register_language(language_info_factoryt factory)
{
  auto language_info = factory();

  // check whether we attempt to register the same language twice
  for(const auto &info : languages)
  {
    PRECONDITION(language_info->id() != info->id());
  }

  languages.push_back(std::move(language_info));
}

/// Unregister all registered languages
void clear_languages()
{
  languages.clear();
}

/// Get the language corresponding to the given mode
/// \param mode: the mode, e.g. `ID_C`
/// \return the language or `nullptr` if the language has not been registered
std::unique_ptr<languaget> get_language_from_mode(const irep_idt &mode)
{
  for(const auto &language_info : languages)
  {
    if(mode == language_info->id())
      return language_info->new_language();
  }

  return nullptr;
}

/// Get the language info corresponding to the given mode
/// \param mode: the mode, e.g. `ID_C`
/// \return the language info (assumes that the language has been registered)
const language_infot &get_language_info_from_mode(const irep_idt &mode)
{
  for(const auto &language_info : languages)
  {
    if(mode == language_info->id())
      return *language_info;
  }

  INVARIANT(false, "unregistered language `" + id2string(mode) + "'");
}

/// Get the mode of the given identifier's symbol
/// \param ns: a namespace
/// \param identifier: an identifier
/// \return the mode, e.g. `ID_C`, if the identifier is in the given
///   symbol table, or `ID_unknown` otherwise
const irep_idt &
get_mode_from_identifier(const namespacet &ns, const irep_idt &identifier)
{
  if(identifier.empty())
    return ID_unknown;
  const symbolt *symbol;
  if(ns.lookup(identifier, symbol))
    return ID_unknown;
  return symbol->mode;
}

/// Get the language info corresponding to the mode of
/// the given identifier's symbol
/// \param ns: a namespace
/// \param identifier: an identifier
/// \return the corresponding language info if the mode is not `ID_unknown`, or
///    the default language otherwise;
/// Note: It is assumed as an invariant that languages of symbols in the symbol
///   table have been registered.
const language_infot &get_language_info_from_identifier(
  const namespacet &ns,
  const irep_idt &identifier)
{
  const irep_idt &mode = get_mode_from_identifier(ns, identifier);
  if(mode == ID_unknown)
    return get_default_language_info();

  return get_language_info_from_mode(mode);
}

/// Get the language corresponding to the mode of
/// the given identifier's symbol
/// \param ns: a namespace
/// \param identifier: an identifier
/// \return the corresponding language info if the mode is not `ID_unknown`, or
///    the default language otherwise;
/// Note: It is assumed as an invariant that languages of symbols in the symbol
///   table have been registered.
std::unique_ptr<languaget>
get_language_from_identifier(const namespacet &ns, const irep_idt &identifier)
{
  const irep_idt &mode = get_mode_from_identifier(ns, identifier);
  if(mode == ID_unknown)
    return get_default_language();

  return get_language_from_mode(mode);
}

/// Get the language corresponding to the registered file name extensions
/// \param filename: a filename
/// \return the corresponding language or `nullptr` if the extension cannot
///   be resolved to any registered language
std::unique_ptr<languaget> get_language_from_filename(
  const std::string &filename)
{
  std::size_t ext_pos=filename.rfind('.');

  if(ext_pos == std::string::npos)
    return nullptr;

  std::string file_extension =
    std::string(filename, ext_pos + 1, std::string::npos);

  if(file_extension.empty())
    return nullptr;

  for(const auto &language_info : languages)
  {
    const auto &extensions = language_info->extensions();
    #ifdef _WIN32
    for(const auto &language_extension : extensions)
    {
      if(_stricmp(file_extension.c_str(), language_extension.c_str()) == 0)
        return language_info->new_language();
    }
    #else
    if(extensions.find(file_extension) != extensions.end())
      return language_info->new_language();
    #endif
  }

  return nullptr;
}

/// Returns the default language
/// \return the first registered language
std::unique_ptr<languaget> get_default_language()
{
  PRECONDITION(!languages.empty());
  const auto &language_info = languages.front();
  return language_info->new_language();
}

/// Returns the default language info
/// \return the info of the first registered language
const language_infot &get_default_language_info()
{
  PRECONDITION(!languages.empty());
  return *languages.front();
}
