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
  bool parse(
    std::istream &instream,
    const std::string &path,
    message_handlert &message_handler) override;

  bool typecheck(
    symbol_tablet &symbol_table,
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

  std::set<std::string> extensions() const override
  {
    return {"json_symtab"};
  }

  std::unique_ptr<languaget> new_language() override
  {
    return util_make_unique<json_symtab_languaget>(get_message_handler());
  }

  bool generate_support_functions(
    symbol_tablet &symbol_table,
    message_handlert &) override
  {
    // check if entry point is already there
    bool entry_point_exists =
      symbol_table.symbols.find(goto_functionst::entry_point()) !=
      symbol_table.symbols.end();
    return !entry_point_exists;
  }

  explicit json_symtab_languaget(message_handlert &message_handler)
    : languaget(message_handler)
  {
  }

  ~json_symtab_languaget() override = default;

protected:
  jsont parsed_json_file;
};

inline std::unique_ptr<languaget> new_json_symtab_language(message_handlert &message_handler)
{
  return util_make_unique<json_symtab_languaget>(message_handler);
}

#endif
