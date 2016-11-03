/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_EXPR2JAVA_H
#define CPROVER_JAVA_BYTECODE_EXPR2JAVA_H

#include <string>
#include <ansi-c/expr2c_class.h>

class exprt;
class namespacet;
class typet;

class expr2javat:public expr2ct
{
public:
  expr2javat(const namespacet &_ns):expr2ct(_ns) { }

  virtual std::string convert(const exprt &src)
  {
    return expr2ct::convert(src);
  }

  virtual std::string convert(const typet &src)
  {
    return expr2ct::convert(src);
  }

protected:
  virtual std::string convert(const exprt &src, unsigned &precedence);
  virtual std::string convert_java_this(const exprt &src, unsigned precedence);
  virtual std::string convert_java_instanceof(const exprt &src, unsigned precedence);
  virtual std::string convert_java_new(const exprt &src, unsigned precedence);
  virtual std::string convert_code_java_delete(const exprt &src, unsigned precedence);
  virtual std::string convert_struct(const exprt &src, unsigned &precedence);
  virtual std::string convert_code(const codet &src, unsigned indent);
  virtual std::string convert_constant(const constant_exprt &src, unsigned &precedence);
  virtual std::string convert_code_function_call(const code_function_callt &src, unsigned indent);

  virtual std::string convert_rec(
    const typet &src,
    const c_qualifierst &qualifiers,
    const std::string &declarator);

  // length of string representation of Java Char
  const std::size_t char_representation_length=14;
};

std::string expr2java(const exprt &expr, const namespacet &ns);
std::string type2java(const typet &type, const namespacet &ns);

#endif // CPROVER_JAVA_BYTECODE_EXPR2JAVA_H
