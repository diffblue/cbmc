/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#ifndef CPROVER_JSIL_JSIL_LANGUAGE_H
#define CPROVER_JSIL_JSIL_LANGUAGE_H

#include <util/language.h>
#include <util/make_unique.h>

#include "jsil_parse_tree.h"

class jsil_languaget:public languaget
{
public:
  bool preprocess(
    std::istream &instream,
    const std::string &path,
    std::ostream &outstream) override;

  bool parse(
    std::istream &instream,
    const std::string &path) override;

  bool typecheck(
    symbol_tablet &context,
    const std::string &module) override;

  bool final(symbol_tablet &context) override;

  void show_parse(std::ostream &out) override;

  jsil_languaget() { }
  ~jsil_languaget();

  bool from_expr(
    const exprt &expr,
    std::string &code,
    const namespacet &ns) override;

  bool from_type(
    const typet &type,
    std::string &code,
    const namespacet &ns) override;

  bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    const namespacet &ns) override;

  std::unique_ptr<languaget> new_language() override
  { return util_make_unique<jsil_languaget>(); }

  std::string id() const override { return "jsil"; }
  std::string description() const override
  { return "Javascript Intermediate Language"; }
  std::set<std::string> extensions() const override;

  void modules_provided(std::set<std::string> &modules) override;
  bool interfaces(symbol_tablet &symbol_table) override;

protected:
  jsil_parse_treet parse_tree;
  std::string parse_path;
};

std::unique_ptr<languaget> new_jsil_language();

#endif // CPROVER_JSIL_JSIL_LANGUAGE_H
