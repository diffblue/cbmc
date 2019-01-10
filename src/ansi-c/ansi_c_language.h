/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_ANSI_C_LANGUAGE_H
#define CPROVER_ANSI_C_ANSI_C_LANGUAGE_H

#include <memory>

#include <util/make_unique.h>

#include <langapi/language.h>

#include "ansi_c_parse_tree.h"
#include "c_object_factory_parameters.h"

// clang-format off
#define OPT_ANSI_C_LANGUAGE \
  "(max-nondet-tree-depth):" \
  "(min-null-tree-depth):" \
  "(pointers-to-treat-as-arrays):" \
  "(associated-array-sizes):" \
  "(max-dynamic-array-size):" \

#define HELP_ANSI_C_LANGUAGE \
  " --max-nondet-tree-depth N    limit size of nondet (e.g. input) object tree;\n" /* NOLINT(*) */\
  "                              at level N pointers are set to null\n" \
  " --min-null-tree-depth N      minimum level at which a pointer can first be\n" /* NOLINT(*) */\
  "                              NULL in a recursively nondet initialized struct\n" /* NOLINT(*) */\
  " --pointers-to-treat-as-arrays <identifier,...>  comma separated list of\n" \
  "                               identifiers that should be initialized as arrays\n" /* NOLINT(*) */ \
  " --associated-array-sizes <identifier:identifier...>\n" \
  "                               comma separated list of colon separated pairs\n" /* NOLINT(*) */ \
  "                               of identifiers; The first element of the pair \n" /* NOLINT(*) */ \
  "                               should be the name of an array pointer \n" \
  "                               (see --pointers-to-treat-as-arrays),\n" \
  "                               the second an integer parameter that\n" \
  "                               should hold its size\n" \
  " --max-dynamic-array-size <size>  max size for dynamically allocated arrays\n" /* NOLINT(*) */
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

  bool generate_support_functions(
    symbol_tablet &symbol_table) override;

  bool typecheck(
    symbol_tablet &symbol_table,
    const std::string &module) override;

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
  { return util_make_unique<ansi_c_languaget>(); }

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
