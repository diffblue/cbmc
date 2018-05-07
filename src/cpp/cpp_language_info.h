/*******************************************************************\

Module: C++ Language

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CPP_CPP_LANGUAGE_INFO_H
#define CPROVER_CPP_CPP_LANGUAGE_INFO_H

#include <memory>

#include <langapi/language_info.h>

class cpp_language_infot : public language_infot
{
public:
  explicit cpp_language_infot(language_factoryt _factory)
    : language_infot(_factory)
  {
  }

  bool from_expr(const exprt &expr, std::string &code, const namespacet &ns)
    const override;

  bool from_type(const typet &type, std::string &code, const namespacet &ns)
    const override;

  bool type_to_name(const typet &type, std::string &name, const namespacet &ns)
    const override;

  irep_idt id() const override
  {
    return ID_cpp;
  }
  std::string description() const override
  {
    return "C++";
  }
  std::set<std::string> extensions() const override;
};

std::unique_ptr<language_infot> new_cpp_language_info();

#endif // CPROVER_CPP_CPP_LANGUAGE_INFO_H
