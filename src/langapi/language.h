/*******************************************************************\

Module: Abstract interface to support a programming language

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstract interface to support a programming language

#ifndef CPROVER_LANGAPI_LANGUAGE_H
#define CPROVER_LANGAPI_LANGUAGE_H

#include <iosfwd>
#include <memory> // unique_ptr
#include <set>
#include <string>
#include <unordered_set>

#include <util/message.h>
#include <util/std_types.h>
#include <util/symbol.h>
#include <util/symbol_table_base.h>

class symbol_tablet;
class exprt;
class namespacet;
class optionst;
class typet;

#define OPT_FUNCTIONS \
  "(function):"

#define HELP_FUNCTIONS \
  " --function name              set main function name\n"

class languaget:public messaget
{
public:
  /// Set language-specific options
  virtual void set_language_options(const optionst &)
  {
  }

  // parse file

  virtual bool preprocess(
    std::istream &instream,
    const std::string &path,
    std::ostream &outstream)
  {
    // unused parameters
    (void)instream;
    (void)path;
    (void)outstream;
    return false;
  }

  virtual bool parse(
    std::istream &instream,
    const std::string &path)=0;

  /// Create language-specific support functions, such as __CPROVER_start,
  /// __CPROVER_initialize and language-specific library functions.
  /// This runs after the `typecheck` phase but before lazy function loading.
  /// Anything that must wait until lazy function loading is done can be
  /// deferred until `final`, which runs after lazy function loading is
  /// complete. Functions introduced here are visible to lazy loading and
  /// can influence its decisions (e.g. picking the types of input parameters
  /// and globals), whereas anything introduced during `final` cannot.
  virtual bool generate_support_functions(
    symbol_tablet &symbol_table)=0;

  // add external dependencies of a given module to set

  virtual void dependencies(
    const std::string &module,
    std::set<std::string> &modules);

  // add modules provided by currently parsed file to set

  virtual void modules_provided(std::set<std::string> &modules)
  {
    (void)modules; // unused parameter
  }

  /// Should fill `methods` with the symbol identifiers of all methods this
  /// `languaget` can provide a body for, but doesn't populate that body in
  /// languaget::typecheck (i.e. there is no need to mention methods whose
  /// bodies are eagerly generated). It should be prepared to handle a
  /// `convert_lazy_method` call for any symbol added to `methods`.
  virtual void methods_provided(std::unordered_set<irep_idt> &methods) const
  {
    (void)methods; // unused parameter
  }

  /// Requests this `languaget` should populate the body of method `function_id`
  /// in `symbol_table`. This will only be called if `methods_provided`
  /// advertised the given `function_id` could be provided by this `languaget`
  /// instance.
  virtual void
  convert_lazy_method(
    const irep_idt &function_id, symbol_table_baset &symbol_table)
  {
    // unused parameters
    (void)function_id;
    (void)symbol_table;
  }

  /// Final adjustments, e.g. initializing stub functions and globals that
  /// were discovered during function loading
  virtual bool final(symbol_table_baset &symbol_table);

  // type check interfaces of currently parsed file

  virtual bool interfaces(
    symbol_tablet &symbol_table);

  // type check a module in the currently parsed file

  virtual bool typecheck(
    symbol_tablet &symbol_table,
    const std::string &module)=0;

  // language id / description

  virtual std::string id() const { return ""; }
  virtual std::string description() const { return ""; }
  virtual std::set<std::string> extensions() const
  { return std::set<std::string>(); }

  // show parse tree

  virtual void show_parse(std::ostream &out)=0;

  // conversion of expressions

  /// Formats the given expression in a language-specific way
  /// \param expr: the expression to format
  /// \param code: the formatted expression
  /// \param ns: a namespace
  /// \return false if conversion succeeds
  virtual bool from_expr(
    const exprt &expr,
    std::string &code,
    const namespacet &ns);

  /// Formats the given type in a language-specific way
  /// \param type: the type to format
  /// \param code: the formatted type
  /// \param ns: a namespace
  /// \return false if conversion succeeds
  virtual bool from_type(
    const typet &type,
    std::string &code,
    const namespacet &ns);

  /// Encodes the given type in a language-specific way
  /// \param type: the type to encode
  /// \param name: the encoded type
  /// \param ns: a namespace
  /// \return false if the conversion succeeds
  virtual bool type_to_name(
    const typet &type,
    std::string &name,
    const namespacet &ns);

  /// Parses the given string into an expression
  /// \param code: the string to parse
  /// \param module: prefix to be used for identifiers
  /// \param expr: the parsed expression
  /// \param ns: a namespace
  /// \return false if the conversion succeeds
  virtual bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    const namespacet &ns)=0;

  virtual std::unique_ptr<languaget> new_language()=0;

  // constructor / destructor

  languaget() { }
  virtual ~languaget() { }

protected:
  bool language_options_initialized=false;
};

#endif // CPROVER_UTIL_LANGUAGE_H
