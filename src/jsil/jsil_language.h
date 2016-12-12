/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#ifndef CPROVER_JSIL_JSIL_LANGUAGE_H
#define CPROVER_JSIL_JSIL_LANGUAGE_H

#include <memory>

#include <util/language.h>
#include <util/make_unique.h>

#include "jsil_parse_tree.h"

class jsil_languaget:public languaget
{
public:
  virtual bool preprocess(
    std::istream &instream,
    const std::string &path,
    std::ostream &outstream);

  virtual bool parse(
    std::istream &instream,
    const std::string &path);

  virtual bool typecheck(
    symbol_tablet &context,
    const std::string &module);

  virtual bool final(symbol_tablet &context);

  virtual void show_parse(std::ostream &out);

  virtual ~jsil_languaget();
  jsil_languaget() { }

  virtual bool from_expr(
    const exprt &expr,
    std::string &code,
    const namespacet &ns);

  virtual bool from_type(
    const typet &type,
    std::string &code,
    const namespacet &ns);

  virtual bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    const namespacet &ns);

  virtual std::unique_ptr<languaget> new_language()
  { return util_make_unique<jsil_languaget>(); }

  virtual std::string id() const { return "jsil"; }
  virtual std::string description() const
  { return "Javascript Intermediate Language"; }
  virtual std::set<std::string> extensions() const;

  virtual void modules_provided(std::set<std::string> &modules);
  virtual bool interfaces(symbol_tablet &symbol_table);

  virtual bool generate_start_function(
    const class symbolt &entry_function_symbol,
    class symbol_tablet &symbol_table) override;

protected:
  jsil_parse_treet parse_tree;
  std::string parse_path;
};

std::unique_ptr<languaget> new_jsil_language();

#endif // CPROVER_JSIL_JSIL_LANGUAGE_H
