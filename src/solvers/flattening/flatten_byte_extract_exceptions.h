/*******************************************************************\

Module: Byte flattening

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_SOLVERS_FLATTENING_FLATTEN_BYTE_EXTRACT_EXCEPTIONS_H
#define CPROVER_SOLVERS_FLATTENING_FLATTEN_BYTE_EXTRACT_EXCEPTIONS_H

#include <sstream>
#include <stdexcept>
#include <string>

#include <util/std_expr.h>
#include <util/std_types.h>

class flatten_byte_extract_exceptiont : public std::runtime_error
{
public:
  explicit flatten_byte_extract_exceptiont(const std::string &exception_message)
    : runtime_error(exception_message)
  {
  }
};

class non_const_array_sizet : public flatten_byte_extract_exceptiont
{
public:
  non_const_array_sizet(const array_typet &array_type, const exprt &max_bytes)
    : flatten_byte_extract_exceptiont("cannot unpack array of non-const size"),
      max_bytes(max_bytes),
      array_type(array_type)
  {
    std::ostringstream error_message;
    error_message << runtime_error::what() << "\n";
    error_message << "array_type: " << array_type.pretty();
    error_message << "\nmax_bytes: " << max_bytes.pretty();
    computed_error_message = error_message.str();
  }

  const char *what() const optional_noexcept override
  {
    return computed_error_message.c_str();
  }

private:
  exprt max_bytes;
  array_typet array_type;

  std::string computed_error_message;
};

class non_byte_alignedt : public flatten_byte_extract_exceptiont
{
public:
  non_byte_alignedt(
    const struct_typet &struct_type,
    const struct_union_typet::componentt &component,
    const mp_integer &byte_width)
    : flatten_byte_extract_exceptiont(
        "cannot unpack struct with non-byte aligned components"),
      struct_type(struct_type),
      component(component),
      byte_width(byte_width)
  {
    std::ostringstream error_message;
    error_message << runtime_error::what() << "\n";
    error_message << "width: " << byte_width << "\n";
    error_message << "component:" << component.get_name() << "\n";
    error_message << "struct_type: " << struct_type.pretty();
    computed_error_message = error_message.str();
  }

  const char *what() const optional_noexcept override
  {
    return computed_error_message.c_str();
  }

private:
  const struct_typet struct_type;
  const struct_union_typet::componentt component;
  const mp_integer byte_width;

  std::string computed_error_message;
};

class non_constant_widtht : public flatten_byte_extract_exceptiont
{
public:
public:
  non_constant_widtht(const exprt &src, const exprt &max_bytes)
    : flatten_byte_extract_exceptiont(
        "cannot unpack object of non-constant width"),
      src(src),
      max_bytes(max_bytes)
  {
    std::ostringstream error_message;
    error_message << runtime_error::what() << "\n";
    error_message << "array_type: " << src.pretty();
    error_message << "\nmax_bytes: " << max_bytes.pretty();
    computed_error_message = error_message.str();
  }

  const char *what() const optional_noexcept override
  {
    return computed_error_message.c_str();
  }

private:
  exprt src;
  exprt max_bytes;

  std::string computed_error_message;
};

class non_const_byte_extraction_sizet : public flatten_byte_extract_exceptiont
{
public:
  explicit non_const_byte_extraction_sizet(
    const byte_extract_exprt &unpack_expr)
    : flatten_byte_extract_exceptiont(
        "byte_extract flatting with non-constant size"),
      unpack_expr(unpack_expr)
  {
    std::ostringstream error_message;
    error_message << runtime_error::what() << "\n";
    error_message << "unpack_expr: " << unpack_expr.pretty();
    computed_error_message = error_message.str();
  }

  const char *what() const optional_noexcept override
  {
    return computed_error_message.c_str();
  }

private:
  const byte_extract_exprt unpack_expr;

  std::string computed_error_message;
};

#endif // CPROVER_SOLVERS_FLATTENING_FLATTEN_BYTE_EXTRACT_EXCEPTIONS_H
