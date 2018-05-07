/*******************************************************************\

Module: Language frontend info interface

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Language frontend info interface

#ifndef CPROVER_LANGAPI_LANGUAGE_INFO_H
#define CPROVER_LANGAPI_LANGUAGE_INFO_H

#include <iosfwd>
#include <memory>
#include <set>
#include <string>
#include <unordered_set>

#include <util/std_types.h>
#include <util/symbol.h>

class languaget;
class language_infot;

typedef std::unique_ptr<languaget> (*language_factoryt)(const language_infot &);
typedef std::unique_ptr<language_infot> (*language_info_factoryt)();

class language_infot
{
public:
  /// \return the language's id (aka mode)
  virtual irep_idt id() const = 0;

  /// \return a textual description of the language
  virtual std::string description() const = 0;

  /// \return a set of file extensions associated with this language
  virtual std::set<std::string> extensions() const = 0;

  /// Formats the given expression in a language-specific way
  /// \param expr: the expression to format
  /// \param code: the formatted expression
  /// \param ns: a namespace
  /// \return false if conversion succeeds
  virtual bool
  from_expr(const exprt &expr, std::string &code, const namespacet &ns) const;

  /// Formats the given type in a language-specific way
  /// \param type: the type to format
  /// \param code: the formatted type
  /// \param ns: a namespace
  /// \return false if conversion succeeds
  virtual bool
  from_type(const typet &type, std::string &code, const namespacet &ns) const;

  /// Encodes the given type in a language-specific way
  /// \param type: the type to encode
  /// \param name: the encoded type
  /// \param ns: a namespace
  /// \return false if the conversion succeeds
  virtual bool type_to_name(
    const typet &type,
    std::string &name,
    const namespacet &ns) const;

  virtual ~language_infot() = default;

  /// \return a new language instance
  std::unique_ptr<languaget> new_language() const;

protected:
  const language_factoryt factory;

  explicit language_infot(language_factoryt _factory) : factory(_factory)
  {
  }
};

#endif // CPROVER_UTIL_LANGUAGE_INFO_H
