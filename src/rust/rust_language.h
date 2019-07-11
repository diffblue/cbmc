/*******************************************************************\

Module: Rust Language

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/
// Adapted from the similarly named file in the jsil directory

/// \file
/// Rust Language

#ifndef CPROVER_RUST_RUST_LANGUAGE_H
#define CPROVER_RUST_RUST_LANGUAGE_H

#include <memory>

#include <util/make_unique.h>

#include <langapi/language.h>

#include "rust_parse_tree.h"

class rust_languaget : public languaget
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

  virtual ~rust_languaget();
  rust_languaget()
  {
  }

  bool from_expr(const exprt &expr, std::string &code, const namespacet &ns)
    override;

  bool from_type(const typet &type, std::string &code, const namespacet &ns)
    override;

  bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    const namespacet &ns) override;

  std::unique_ptr<languaget> new_language() override
  {
    return util_make_unique<rust_languaget>();
  }

  std::string id() const override
  {
    return "rust";
  }
  std::string description() const override
  {
    return "Rust";
  }
  std::set<std::string> extensions() const override;

  void modules_provided(std::set<std::string> &modules) override;
  bool interfaces(symbol_tablet &symbol_table) override;

protected:
  rust_parse_treet parse_tree;
  std::string parse_path;
};

std::unique_ptr<languaget> new_rust_language();

#endif // CPROVER_RUST_RUST_LANGUAGE_H
