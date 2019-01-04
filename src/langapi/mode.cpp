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

#include <util/invariant.h>
#include <util/namespace.h>

struct language_entryt
{
  language_factoryt factory;
  std::set<std::string> extensions;
  irep_idt mode;
};

typedef std::list<language_entryt> languagest;
languagest languages;

/// Register a language
/// Note: registering a language is required for using the functions
///   in language_util.h
/// \param factory: a language factory, e.g. `new_ansi_c_language`
void register_language(language_factoryt factory)
{
  languages.push_back(language_entryt());
  std::unique_ptr<languaget> l(factory());
  languages.back().factory=factory;
  languages.back().extensions=l->extensions();
  languages.back().mode=l->id();
}

/// Get the language corresponding to the given mode
/// \param mode: the mode, e.g. `ID_C`
/// \return the language or `nullptr` if the language has not been registered
std::unique_ptr<languaget> get_language_from_mode(const irep_idt &mode)
{
  for(const auto &language : languages)
    if(mode == language.mode)
      return language.factory();

  return nullptr;
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

/// Get the language corresponding to the mode of the given identifier's symbol
/// \param ns: a namespace
/// \param identifier: an identifier
/// \return the corresponding language if the mode is not `ID_unknown`, or
///   the default language otherwise;
/// Note: It is assumed as an invariant that languages of symbols in the symbol
///   table have been registered.
std::unique_ptr<languaget>
get_language_from_identifier(const namespacet &ns, const irep_idt &identifier)
{
  const irep_idt &mode = get_mode_from_identifier(ns, identifier);
  if(mode == ID_unknown)
    return get_default_language();

  std::unique_ptr<languaget> language = get_language_from_mode(mode);
  INVARIANT(
    language,
    "symbol `" + id2string(identifier) + "' has unknown mode '" +
      id2string(mode) + "'");
  return language;
}

/// Get the language corresponding to the registered file name extensions
/// \param filename: a filename
/// \return the corresponding language or `nullptr` if the extension cannot
///   be resolved to any registered language
std::unique_ptr<languaget> get_language_from_filename(
  const std::string &filename)
{
  std::size_t ext_pos=filename.rfind('.');

  if(ext_pos==std::string::npos)
    return nullptr;

  std::string extension=
    std::string(filename, ext_pos+1, std::string::npos);

  if(extension=="")
    return nullptr;

  for(languagest::const_iterator
      l_it=languages.begin();
      l_it!=languages.end();
      l_it++)
  {
    #ifdef _WIN32
    for(std::set<std::string>::const_iterator
        e_it=l_it->extensions.begin();
        e_it!=l_it->extensions.end();
        e_it++)
      if(_stricmp(extension.c_str(), e_it->c_str())==0)
        return l_it->factory();
    #else
    if(l_it->extensions.find(extension)!=l_it->extensions.end())
      return l_it->factory();
    #endif
  }

  return nullptr;
}

/// Returns the default language
/// \return the first registered language
std::unique_ptr<languaget> get_default_language()
{
  PRECONDITION(!languages.empty());
  return languages.front().factory();
}
