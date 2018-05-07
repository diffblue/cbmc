/*******************************************************************\

Module: C Language

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_ANSI_C_LANGUAGE_INFO_H
#define CPROVER_ANSI_C_ANSI_C_LANGUAGE_INFO_H

#include <memory>

#include <langapi/language_info.h>

class ansi_c_language_infot : public language_infot
{
public:
  explicit ansi_c_language_infot(language_factoryt _factory)
    : language_infot(_factory)
  {
  }

  irep_idt id() const override
  {
    return ID_C;
  }

  std::string description() const override
  {
    return "C";
  }

  std::set<std::string> extensions() const override;

  bool from_expr(const exprt &expr, std::string &code, const namespacet &ns)
    const override;

  bool from_type(const typet &type, std::string &code, const namespacet &ns)
    const override;

  bool type_to_name(const typet &type, std::string &name, const namespacet &ns)
    const override;
};

std::unique_ptr<language_infot> new_ansi_c_language_info();

#endif // CPROVER_ANSI_C_ANSI_C_LANGUAGE_INFO_H
