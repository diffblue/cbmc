/*******************************************************************\

Module: Java Bytecode Language

Author: Diffblue Ltd

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_INFO_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_INFO_H

#include <memory>

#include <langapi/language_info.h>

class java_bytecode_language_infot : public language_infot
{
public:
  explicit java_bytecode_language_infot(language_factoryt _factory)
    : language_infot(_factory)
  {
  }

  bool from_expr(const exprt &expr, std::string &code, const namespacet &ns)
    const override;

  bool from_type(const typet &type, std::string &code, const namespacet &ns)
    const override;

  irep_idt id() const override
  {
    return ID_java;
  }
  std::string description() const override
  {
    return "Java Bytecode";
  }
  std::set<std::string> extensions() const override;
};

std::unique_ptr<language_infot> new_java_bytecode_language_info();

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_INFO_H
