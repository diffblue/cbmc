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

class ansi_c_languaget:public languaget
{
public:
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

  explicit ansi_c_languaget(const language_infot &info) : languaget(info)
  {
  }
  ~ansi_c_languaget() override;

  bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    const namespacet &ns) override;

  void modules_provided(std::set<std::string> &modules) override;

protected:
  ansi_c_parse_treet parse_tree;
  std::string parse_path;
};

std::unique_ptr<languaget> new_ansi_c_language(const language_infot &info);

#endif // CPROVER_ANSI_C_ANSI_C_LANGUAGE_H
