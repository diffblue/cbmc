/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_LANGAPI_LANGUAGES_H
#define CPROVER_LANGAPI_LANGUAGES_H

#include <util/language.h>

#include <memory> // unique_ptr

class languagest
{
public:
  // conversion of expressions

  bool from_expr(const exprt &expr, std::string &code)
  {
    return language->from_expr(expr, code, ns);
  }

  bool from_type(const typet &type, std::string &code)
  {
    return language->from_type(type, code, ns);
  }

  bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr)
  {
    return language->to_expr(code, module, expr, ns);
  }

  // constructor / destructor

  languagest(const namespacet &_ns, std::unique_ptr<languaget> _language):
    ns(_ns),
    language(std::move(_language))
  {
  }

  virtual ~languagest() {}

protected:
  const namespacet &ns;
  std::unique_ptr<languaget> language;
};

#endif // CPROVER_LANGAPI_LANGUAGES_H
