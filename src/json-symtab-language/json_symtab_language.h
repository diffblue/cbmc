/*******************************************************************\

Module: JSON symbol table language. Accepts a JSON format symbol
        table that has been produced out-of-process, e.g. by using
        a compiler's front-end.

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_JSON_SYMTAB_LANGUAGE_JSON_SYMTAB_LANGUAGE_H
#define CPROVER_JSON_SYMTAB_LANGUAGE_JSON_SYMTAB_LANGUAGE_H

#include <util/json.h>
#include <util/symbol_table_base.h>

#include <goto-programs/goto_functions.h>

#include <langapi/language.h>

#include <set>
#include <string>

class json_symtab_languaget : public languaget
{
public:
  bool parse(
    std::istream &instream,
    const std::string &path,
    message_handlert &message_handler) override;

  bool typecheck(
    symbol_table_baset &symbol_table,
    const std::string &module,
    message_handlert &message_handler) override;

  void show_parse(std::ostream &out, message_handlert &) override;

  bool to_expr(
    const std::string &,
    const std::string &,
    exprt &,
    const namespacet &,
    message_handlert &) override
  {
    UNIMPLEMENTED;
  }

  std::string id() const override
  {
    return "json_symtab";
  }
  std::string description() const override
  {
    return "JSON symbol table";
  }

  std::set<std::string> extensions() const override
  {
    return {"json_symtab"};
  }

  std::unique_ptr<languaget> new_language() override
  {
    return std::make_unique<json_symtab_languaget>();
  }

  bool generate_support_functions(
    symbol_table_baset &symbol_table,
    message_handlert &) override
  {
    // check if entry point is already there
    bool entry_point_exists =
      symbol_table.symbols.find(goto_functionst::entry_point()) !=
      symbol_table.symbols.end();
    return !entry_point_exists;
  }

  ~json_symtab_languaget() override = default;

protected:
  jsont parsed_json_file;
};

inline std::unique_ptr<languaget> new_json_symtab_language()
{
  return std::make_unique<json_symtab_languaget>();
}

#endif
