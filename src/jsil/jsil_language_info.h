/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

#ifndef CPROVER_JSIL_JSIL_LANGUAGE_INFO_H
#define CPROVER_JSIL_JSIL_LANGUAGE_INFO_H

#include <memory>

#include <langapi/language_info.h>

class jsil_language_infot : public language_infot
{
public:
  explicit jsil_language_infot(language_factoryt _factory)
    : language_infot(_factory)
  {
  }

  irep_idt id() const override
  {
    return ID_jsil;
  }
  std::string description() const override
  {
    return "Javascript Intermediate Language";
  }
  std::set<std::string> extensions() const override;

  bool from_expr(const exprt &expr, std::string &code, const namespacet &ns)
    const override;

  bool from_type(const typet &type, std::string &code, const namespacet &ns)
    const override;
};

std::unique_ptr<language_infot> new_jsil_language_info();

#endif // CPROVER_JSIL_JSIL_LANGUAGE_INFO_H
