/*******************************************************************\

Module: JSON symbol table language. Accepts a JSON format symbol
        table that has been produced out-of-process, e.g. by using
        a compiler's front-end.

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_JSON_SYMTAB_LANGUAGE_JSON_SYMTAB_LANGUAGE_H
#define CPROVER_JSON_SYMTAB_LANGUAGE_JSON_SYMTAB_LANGUAGE_H

#include <set>
#include <string>

#include <goto-programs/goto_functions.h>
#include <langapi/language.h>
#include <util/json.h>
#include <util/make_unique.h>

class json_symtab_languaget : public languaget
{
public:
  bool parse(std::istream &instream, const std::string &path) override;

  bool
  typecheck(symbol_tablet &symbol_table, const std::string &module) override;

  void show_parse(std::ostream &out) override;

  bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    const namespacet &ns) override
  {
    UNIMPLEMENTED;
  }

  std::set<std::string> extensions() const override
  {
    return {"json_symtab"};
  }

  std::unique_ptr<languaget> new_language() override
  {
    return util_make_unique<json_symtab_languaget>();
  }

  bool generate_support_functions(symbol_tablet &symbol_table) override
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
  return util_make_unique<json_symtab_languaget>();
}

#endif
