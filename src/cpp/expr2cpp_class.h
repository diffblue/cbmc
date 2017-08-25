/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_EXPR2CPP_CLASS_H
#define CPROVER_CPP_EXPR2CPP_CLASS_H

#include <ansi-c/expr2c_class.h>

class expr2cppt:public expr2ct
{
public:
  explicit expr2cppt(const namespacet &_ns):expr2ct(_ns) { }

protected:
  std::string convert_with_precedence(
    const exprt &src,
    unsigned &precedence) override;
  std::string convert_cpp_this(const exprt &src, unsigned precedence);
  std::string convert_cpp_new(const exprt &src, unsigned precedence);
  std::string convert_extractbit(const exprt &src, unsigned precedence);
  std::string convert_extractbits(const exprt &src, unsigned precedence);
  std::string convert_code_cpp_delete(const exprt &src, unsigned precedence);
  std::string convert_struct(const exprt &src, unsigned &precedence) override;
  std::string convert_code(const codet &src, unsigned indent) override;
  // NOLINTNEXTLINE(whitespace/line_length)
  std::string convert_constant(const constant_exprt &src, unsigned &precedence) override;

  std::string convert_rec(
    const typet &src,
    const c_qualifierst &qualifiers,
    const std::string &declarator) override;

  typedef std::unordered_set<std::string, string_hash> id_sett;
};

#endif
