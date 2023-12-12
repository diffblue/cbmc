/*******************************************************************\

Module: C++ Language Module

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Module

#ifndef CPROVER_CPP_CPP_LANGUAGE_H
#define CPROVER_CPP_CPP_LANGUAGE_H

#include <memory>

#include <ansi-c/c_object_factory_parameters.h>

#include <langapi/language.h>

#include "cpp_parse_tree.h"

class cpp_languaget:public languaget
{
public:
  void
  set_language_options(const optionst &options, message_handlert &) override
  {
    object_factory_params.set(options);
  }

  bool preprocess(
    std::istream &instream,
    const std::string &path,
    std::ostream &outstream,
    message_handlert &message_handler) override;

  bool parse(
    std::istream &instream,
    const std::string &path,
    message_handlert &message_handler) override;

  bool generate_support_functions(
    symbol_table_baset &symbol_table,
    message_handlert &message_handler) override;

  bool typecheck(
    symbol_table_baset &symbol_table,
    const std::string &module,
    message_handlert &message_handler) override;

  bool merge_symbol_table(
    symbol_table_baset &dest,
    symbol_table_baset &src,
    const std::string &module,
    class replace_symbolt &replace_symbol) const;

  void show_parse(std::ostream &out, message_handlert &) override;

  // constructor, destructor
  ~cpp_languaget() override;
  cpp_languaget() { }

  // conversion from expression into string
  bool from_expr(
    const exprt &expr,
    std::string &code,
    const namespacet &ns) override;

  // conversion from type into string
  bool from_type(
    const typet &type,
    std::string &code,
    const namespacet &ns) override;

  bool type_to_name(
    const typet &type,
    std::string &name,
    const namespacet &ns) override;

  // conversion from string into expression
  bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    const namespacet &ns,
    message_handlert &message_handler) override;

  std::unique_ptr<languaget> new_language() override
  {
    return std::make_unique<cpp_languaget>();
  }

  std::string id() const override { return "cpp"; }
  std::string description() const override { return "C++"; }
  std::set<std::string> extensions() const override;

  void modules_provided(std::set<std::string> &modules) override;

protected:
  cpp_parse_treet cpp_parse_tree;
  std::string parse_path;

  c_object_factory_parameterst object_factory_params;

  void show_parse(std::ostream &out, const cpp_itemt &item);

  std::string main_symbol()
  {
    return "main";
  }
};

std::unique_ptr<languaget> new_cpp_language();

#endif // CPROVER_CPP_CPP_LANGUAGE_H
