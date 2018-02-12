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

class jsil_languaget:public languaget
{
public:
  virtual bool preprocess(
    std::istream &instream,
    const std::string &path,
    std::ostream &outstream) override;

  virtual bool parse(
    std::istream &instream,
    const std::string &path) override;

  virtual bool generate_support_functions(
    symbol_tablet &symbol_table) override;

  virtual bool typecheck(
    symbol_tablet &context,
    const std::string &module) override;

  virtual void show_parse(std::ostream &out) override;

  virtual ~jsil_languaget();
  jsil_languaget() { }

  virtual bool from_expr(
    const exprt &expr,
    std::string &code,
    const namespacet &ns) override;

  virtual bool from_type(
    const typet &type,
    std::string &code,
    const namespacet &ns) override;

  virtual bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    const namespacet &ns) override;

  virtual std::unique_ptr<languaget> new_language() override
  { return util_make_unique<jsil_languaget>(); }

  virtual std::string id() const override { return "jsil"; }
  virtual std::string description() const override
  { return "Javascript Intermediate Language"; }
  virtual std::set<std::string> extensions() const override;

  virtual void modules_provided(std::set<std::string> &modules) override;
  virtual bool interfaces(symbol_tablet &symbol_table) override;

protected:
  jsil_parse_treet parse_tree;
  std::string parse_path;
};

std::unique_ptr<languaget> new_jsil_language();

#endif // CPROVER_JSIL_JSIL_LANGUAGE_H
