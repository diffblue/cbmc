/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_EXPR2JAVA_H
#define CPROVER_JAVA_BYTECODE_EXPR2JAVA_H

#include <cmath>
#include <numeric>
#include <sstream>
#include <string>
#include <ansi-c/expr2c_class.h>

class expr2javat:public expr2ct
{
public:
  explicit expr2javat(const namespacet &_ns):expr2ct(_ns) { }
protected:
  virtual std::string convert_with_precedence(
    const exprt &src, unsigned &precedence);
  virtual std::string convert_java_this(const exprt &src, unsigned precedence);
  virtual std::string convert_java_instanceof(
    const exprt &src,
    unsigned precedence);
  virtual std::string convert_java_new(const exprt &src, unsigned precedence);
  virtual std::string convert_code_java_delete(
    const exprt &src,
    unsigned precedence);
  virtual std::string convert_struct(const exprt &src, unsigned &precedence);
  virtual std::string convert_code(const codet &src, unsigned indent);
  virtual std::string convert_constant(
    const constant_exprt &src,
    unsigned &precedence);
  virtual std::string convert_code_function_call(
    const code_function_callt &src,
    unsigned indent);

  virtual std::string convert_rec(
    const typet &src,
    const c_qualifierst &qualifiers,
    const std::string &declarator);

  // length of string representation of Java Char
  // representation is '\u0000'
  const std::size_t char_representation_length=8;
};

std::string expr2java(const exprt &expr, const namespacet &ns);
std::string type2java(const typet &type, const namespacet &ns);

/// Convert floating point number to a string without printing
/// unnecessary zeros. Prints decimal if precision is not lost.
/// Prints hexadecimal otherwise, and/or java-friendly NaN and Infinity
template <typename float_type>
std::string floating_point_to_java_string(float_type value)
{
  const auto is_float = std::is_same<float_type, float>::value;
  static const std::string class_name = is_float ? "Float" : "Double";
  if(std::isnan(value))
    return class_name + ".NaN";
  if(std::isinf(value) && value >= 0.)
    return class_name + ".POSITIVE_INFINITY";
  if(std::isinf(value) && value <= 0.)
    return class_name + ".NEGATIVE_INFINITY";
  const std::string decimal = [&]() -> std::string { // NOLINT
    // Using ostringstream instead of to_string to get string without
    // trailing zeros
    std::ostringstream raw_stream;
    raw_stream << value;
    const auto raw_decimal = raw_stream.str();
    if(raw_decimal.find('.') == std::string::npos)
      return raw_decimal + ".0";
    return raw_decimal;
  }();
  const bool is_lossless = [&] { // NOLINT
    if(value == std::numeric_limits<float_type>::min())
      return true;
    try
    {
      return std::stod(decimal) == value;
    }
    catch(std::out_of_range)
    {
      return false;
    }
  }();
  const std::string lossless = [&]() -> std::string { // NOLINT
    if(is_lossless)
      return decimal;
    std::ostringstream stream;
    stream << std::hexfloat << value;
    return stream.str();
  }();
  const auto literal = is_float ? lossless + 'f' : lossless;
  if(is_lossless)
    return literal;
  return literal + " /* " + decimal + " */";
}

#endif // CPROVER_JAVA_BYTECODE_EXPR2JAVA_H
