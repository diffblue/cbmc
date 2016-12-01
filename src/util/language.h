/*******************************************************************\

Module: Abstract interface to support a programming language

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstract interface to support a programming language

#ifndef CPROVER_UTIL_LANGUAGE_H
#define CPROVER_UTIL_LANGUAGE_H

#include <set>
#include <iosfwd>
#include <string>
#include <util/symbol.h>
#include <util/std_types.h>
#include <goto-programs/system_library_symbols.h>

#include "message.h"

class symbol_tablet;
class symbolt;
class exprt;
class namespacet;
class typet;
class cmdlinet;

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

  // add external dependencies of a given module to set

  virtual void dependencies(
    const std::string &module,
    std::set<std::string> &modules);

  // add modules provided by currently parsed file to set

  virtual void modules_provided(std::set<std::string> &modules)
  { }

  // add lazy functions provided to set

  virtual void lazy_methods_provided(std::set<irep_idt> &methods) const
  { }

  // populate a lazy method
  virtual void convert_lazy_method(const irep_idt &id, symbol_tablet &)
  { }

  // final adjustments, e.g., initialization and call to main()

  virtual bool final(
    symbol_tablet &symbol_table);

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

  virtual bool type_to_name(
    const typet &type,
    std::string &name,
    const namespacet &ns);

  virtual bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    const namespacet &ns)=0;

  virtual languaget *new_language()=0;

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

  bool generate_opaque_stubs;
  bool language_options_initialized=false;

private:
  bool is_symbol_opaque_function(const symbolt &symbol);
  void generate_opaque_parameter_symbols(
    symbolt &function_symbol,
    symbol_tablet &symbol_table);

  system_library_symbolst system_symbols;
};
#endif // CPROVER_UTIL_LANGUAGE_H
