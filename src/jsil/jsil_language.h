/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#ifndef CPROVER_JSIL_JSIL_LANGUAGE_H
#define CPROVER_JSIL_JSIL_LANGUAGE_H

#include <memory>

#include <util/make_unique.h>

#include <langapi/language.h>

#include "jsil_parse_tree.h"

#include "jsil_language_info.h"

class jsil_languaget:public languaget
{
public:
  bool preprocess(
    std::istream &instream,
    const std::string &path,
    std::ostream &outstream) override;

  bool parse(std::istream &instream, const std::string &path) override;

  bool generate_support_functions(symbol_tablet &symbol_table) override;

  bool typecheck(symbol_tablet &context, const std::string &module) override;

  void show_parse(std::ostream &out) override;

  ~jsil_languaget();
  explicit jsil_languaget(const language_infot &info) : languaget(info)
  {
  }

  bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    const namespacet &ns) override;

  void modules_provided(std::set<std::string> &modules) override;
  bool interfaces(symbol_tablet &symbol_table) override;

protected:
  jsil_parse_treet parse_tree;
  std::string parse_path;
};

std::unique_ptr<languaget> new_jsil_language(const language_infot &);

#endif // CPROVER_JSIL_JSIL_LANGUAGE_H
