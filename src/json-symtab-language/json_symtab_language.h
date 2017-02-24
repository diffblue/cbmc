/*******************************************************************\

Module: JSON symbol table language. Accepts a JSON format symbol
        table that has been produced out-of-process, e.g. by using
        a compiler's front-end.

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_JSON_SYMTAB_LANGUAGE_JSON_SYMTAB_LANGUAGE_H
#define CPROVER_JSON_SYMTAB_LANGUAGE_JSON_SYMTAB_LANGUAGE_H

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
    // Not implemented.
    return true;
  }

  virtual std::set<std::string> extensions() const override
  {
    return {"json_symtab"};
  }

  std::unique_ptr<languaget> new_language() override
  {
    return util_make_unique<json_symtab_languaget>();
  }

  bool generate_support_functions(symbol_tablet &symbol_table) override
  {
    // TODO: Is this correct?
    return true;
  }

protected:
  jsont parsed_json_file;
};

inline std::unique_ptr<languaget> new_json_symtab_language()
{
  return util_make_unique<json_symtab_languaget>();
}

#endif
