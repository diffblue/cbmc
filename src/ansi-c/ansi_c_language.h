/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_ANSI_C_LANGUAGE_H
#define CPROVER_ANSI_C_ANSI_C_LANGUAGE_H

#include <memory>

#include <langapi/language.h>

#include "ansi_c_parse_tree.h"
#include "c_object_factory_parameters.h"

// clang-format off
#define OPT_ANSI_C_LANGUAGE \
  "(max-nondet-tree-depth):" \
  "(min-null-tree-depth):"

#define HELP_ANSI_C_LANGUAGE \
  " {y--max-nondet-tree-depth} {uN} \t " \
  "limit size of nondet (e.g. input) object tree; at level {uN} pointers are " \
  "set to null\n" \
  " {y--min-null-tree-depth} {uN} \t " \
  "minimum level at which a pointer can first be NULL in a recursively " \
  "nondet initialized struct\n" \
// clang-format on

class ansi_c_languaget:public languaget
{
public:
  void set_language_options(const optionst &options) override
  {
    object_factory_params.set(options);
  }

  bool preprocess(
    std::istream &instream,
    const std::string &path,
    std::ostream &outstream) override;

  bool parse(
    std::istream &instream,
    const std::string &path) override;

  bool generate_support_functions(symbol_table_baset &symbol_table) override;

  bool typecheck(
    symbol_table_baset &symbol_table,
    const std::string &module,
    const bool keep_file_local) override;

  bool typecheck(
    symbol_table_baset &symbol_table,
    const std::string &module,
    const bool keep_file_local,
    const std::set<irep_idt> &keep);

  bool can_keep_file_local() override
  {
    return true;
  }

  bool typecheck(symbol_table_baset &symbol_table, const std::string &module)
    override
  {
    return typecheck(symbol_table, module, true);
  }

  void show_parse(std::ostream &out) override;

  ~ansi_c_languaget() override;
  ansi_c_languaget() { }

  bool from_expr(
    const exprt &expr,
    std::string &code,
    const namespacet &ns) override;

  bool from_type(
    const typet &type,
    std::string &code,
    const namespacet &ns) override;

  bool type_to_name(
    const typet &type,
    std::string &name,
    const namespacet &ns) override;

  bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    const namespacet &ns) override;

  std::unique_ptr<languaget> new_language() override
  {
    return std::make_unique<ansi_c_languaget>();
  }

  std::string id() const override { return "C"; }
  std::string description() const override { return "ANSI-C 99"; }
  std::set<std::string> extensions() const override;

  void modules_provided(std::set<std::string> &modules) override;

protected:
  ansi_c_parse_treet parse_tree;
  std::string parse_path;

  c_object_factory_parameterst object_factory_params;
};

std::unique_ptr<languaget> new_ansi_c_language();

#endif // CPROVER_ANSI_C_ANSI_C_LANGUAGE_H
