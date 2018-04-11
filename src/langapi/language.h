/*******************************************************************\

Module: Abstract interface to support a programming language

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstract interface to support a programming language

#ifndef CPROVER_LANGAPI_LANGUAGE_H
#define CPROVER_LANGAPI_LANGUAGE_H

#include <unordered_set>
#include <iosfwd>
#include <string>
#include <memory> // unique_ptr

#include <util/symbol.h>
#include <util/std_types.h>
#include <util/message.h>

#include <goto-programs/system_library_symbols.h>

typedef std::unordered_set<irep_idt, irep_id_hash> id_sett;

class symbol_tablet;
class symbol_table_baset;
class exprt;
class namespacet;
class typet;
class cmdlinet;
class json_objectt;

#define OPT_FUNCTIONS \
  "(function):"

#define HELP_FUNCTIONS \
  " --function name              set main function name\n"

class languaget:public messaget
{
public:
  // Parse language-specific options
  virtual void get_language_options(const cmdlinet &) {}

  // parse file

  virtual bool preprocess(
    std::istream &instream,
    const std::string &path,
    std::ostream &outstream) { return false; }

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
  { }

  // add lazy functions provided to set

  virtual void methods_provided(id_sett &methods) const
  { }

  // populate a lazy method
  virtual void
  convert_lazy_method(
    const irep_idt &function_id, symbol_table_baset &symbol_table)
  { }

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

  virtual bool from_expr(
    const exprt &expr,
    std::string &code,
    const namespacet &ns);

  virtual bool from_type(
    const typet &type,
    std::string &code,
    const namespacet &ns);

  virtual json_objectt json(
    const exprt &,
    const namespacet &);

  virtual json_objectt json(
    const typet &,
    const namespacet &);

  virtual json_objectt json(const source_locationt &);

  virtual bool type_to_name(
    const typet &type,
    std::string &name,
    const namespacet &ns);

  virtual bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    const namespacet &ns)=0;

  /// returns the class type that contains RTTI
  virtual symbol_typet root_base_class_type() = 0;

  virtual std::unique_ptr<languaget> new_language()=0;

  void set_should_generate_opaque_method_stubs(bool should_generate_stubs);

  // constructor / destructor

  languaget() { }
  virtual ~languaget() { }

protected:
  void generate_opaque_method_stubs(symbol_tablet &symbol_table);
  virtual irep_idt generate_opaque_stub_body(
    symbolt &symbol,
    symbol_tablet &symbol_table);

  virtual parameter_symbolt build_stub_parameter_symbol(
    const symbolt &function_symbol,
    size_t parameter_index,
    const code_typet::parametert &parameter);

  static irep_idt get_stub_return_symbol_name(const irep_idt &function_id);

  bool generate_opaque_stubs=false;
  bool language_options_initialized=false;

private:
  bool is_symbol_opaque_function(const symbolt &symbol);
  void generate_opaque_parameter_symbols(
    symbolt &function_symbol,
    symbol_tablet &symbol_table);

  system_library_symbolst system_symbols;
};
#endif // CPROVER_UTIL_LANGUAGE_H
