/*******************************************************************\

Module: printf Formatting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// printf Formatting

#include "printf_formatter.h"

#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/format_constant.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include <sstream>

const exprt printf_formattert::make_type(const exprt &src, const typet &dest)
{
  if(src.type() == dest)
    return src;
  return simplify_expr(typecast_exprt(src, dest), ns);
}

void printf_formattert::operator()(
  const std::string &_format,
  const std::list<exprt> &_operands)
{
  format = _format;
  operands = _operands;
}

void printf_formattert::print(std::ostream &out)
{
  format_pos = 0;
  next_operand = operands.begin();

  try
  {
    while(!eol())
      process_char(out);
  }

  catch(const eol_exceptiont &)
  {
  }
}

std::string printf_formattert::as_string()
{
  std::ostringstream stream;
  print(stream);
  return stream.str();
}

void printf_formattert::process_format(std::ostream &out)
{
  exprt tmp;
  format_constantt format_constant;

  format_constant.precision = 6;
  format_constant.min_width = 0;
  format_constant.zero_padding = false;

  std::string length_modifier;

  char ch = next();

  if(ch == '0') // leading zeros
  {
    format_constant.zero_padding = true;
    ch = next();
  }

  while(isdigit(ch)) // width
  {
    format_constant.min_width *= 10;
    format_constant.min_width += ch - '0';
    ch = next();
  }

  if(ch == '.') // precision
  {
    format_constant.precision = 0;
    ch = next();

    while(isdigit(ch))
    {
      format_constant.precision *= 10;
      format_constant.precision += ch - '0';
      ch = next();
    }
  }

  switch(ch)
  {
  case 'h':
    ch = next();
    if(ch == 'h')
    {
      length_modifier = "hh";
      ch = next();
    }
    else
    {
      length_modifier = "h";
    }
    break;

  case 'l':
    ch = next();
    if(ch == 'l')
    {
      length_modifier = "ll";
      ch = next();
    }
    else
    {
      length_modifier = "l";
    }
    break;

  case 'q':
    ch = next();
    length_modifier = "ll";
    break;

  case 'L':
  case 'j':
  case 'z':
  case 't':
    length_modifier = ch;
    ch = next();
    break;

  case 'Z':
    ch = next();
    length_modifier = "z";
    break;

  default:
    break;
  }

  switch(ch)
  {
  case '%':
    out << ch;
    break;

  case 'e':
  case 'E':
    format_constant.style = format_spect::stylet::SCIENTIFIC;
    if(next_operand == operands.end())
      break;
    if(length_modifier == "L")
      out << format_constant(make_type(*(next_operand++), long_double_type()));
    else
      out << format_constant(make_type(*(next_operand++), double_type()));
    break;

  case 'a': // TODO: hexadecimal output
  case 'A': // TODO: hexadecimal output
  case 'f':
  case 'F':
    format_constant.style = format_spect::stylet::DECIMAL;
    if(next_operand == operands.end())
      break;
    if(length_modifier == "L")
      out << format_constant(make_type(*(next_operand++), long_double_type()));
    else
      out << format_constant(make_type(*(next_operand++), double_type()));
    break;

  case 'g':
  case 'G':
    format_constant.style = format_spect::stylet::AUTOMATIC;
    if(format_constant.precision == 0)
      format_constant.precision = 1;
    if(next_operand == operands.end())
      break;
    if(length_modifier == "L")
      out << format_constant(make_type(*(next_operand++), long_double_type()));
    else
      out << format_constant(make_type(*(next_operand++), double_type()));
    break;

  case 'S':
    length_modifier = 'l';
  case 's':
  {
    if(next_operand == operands.end())
      break;
    // this is the address of a string
    const exprt &op = *(next_operand++);
    if(
      auto pointer_constant =
        expr_try_dynamic_cast<annotated_pointer_constant_exprt>(op))
    {
      if(
        auto address_of = expr_try_dynamic_cast<address_of_exprt>(
          skip_typecast(pointer_constant->symbolic_pointer())))
      {
        if(address_of->object().id() == ID_string_constant)
        {
          out << format_constant(address_of->object());
        }
        else if(
          auto index_expr =
            expr_try_dynamic_cast<index_exprt>(address_of->object()))
        {
          if(
            index_expr->index().is_zero() &&
            index_expr->array().id() == ID_string_constant)
          {
            out << format_constant(index_expr->array());
          }
        }
      }
    }
  }
  break;

  case 'd':
  case 'i':
  {
    if(next_operand == operands.end())
      break;
    typet conversion_type;
    if(length_modifier == "hh")
      conversion_type = signed_char_type();
    else if(length_modifier == "h")
      conversion_type = signed_short_int_type();
    else if(length_modifier == "l")
      conversion_type = signed_long_int_type();
    else if(length_modifier == "ll")
      conversion_type = signed_long_long_int_type();
    else if(length_modifier == "j") // intmax_t
      conversion_type = signed_long_long_int_type();
    else if(length_modifier == "z")
      conversion_type = signed_size_type();
    else if(length_modifier == "t")
      conversion_type = pointer_diff_type();
    else
      conversion_type = signed_int_type();
    out << format_constant(make_type(*(next_operand++), conversion_type));
  }
  break;

  case 'o': // TODO: octal output
  case 'x': // TODO: hexadecimal output
  case 'X': // TODO: hexadecimal output
  case 'u':
  {
    if(next_operand == operands.end())
      break;
    typet conversion_type;
    if(length_modifier == "hh")
      conversion_type = unsigned_char_type();
    else if(length_modifier == "h")
      conversion_type = unsigned_short_int_type();
    else if(length_modifier == "l")
      conversion_type = unsigned_long_int_type();
    else if(length_modifier == "ll")
      conversion_type = unsigned_long_long_int_type();
    else if(length_modifier == "j") // intmax_t
      conversion_type = unsigned_long_long_int_type();
    else if(length_modifier == "z")
      conversion_type = size_type();
    else if(length_modifier == "t")
      conversion_type = pointer_diff_type();
    else
      conversion_type = unsigned_int_type();
    out << format_constant(make_type(*(next_operand++), conversion_type));
  }
  break;

  case 'C':
    length_modifier = 'l';
  case 'c':
    if(next_operand == operands.end())
      break;
    if(length_modifier == "l")
      out << format_constant(make_type(*(next_operand++), wchar_t_type()));
    else
      out << format_constant(
        make_type(*(next_operand++), unsigned_char_type()));
    break;

  case 'p':
    // TODO: hexadecimal output
    out << format_constant(make_type(*(next_operand++), size_type()));
    break;

  case 'n':
    if(next_operand == operands.end())
      break;
    // printf would store the number of characters written so far in the
    // object pointed to by this operand. We do not implement this side-effect
    // here, and just skip one operand.
    ++next_operand;
    break;

  default:
    out << '%' << ch;
  }
}

void printf_formattert::process_char(std::ostream &out)
{
  char ch = next();

  if(ch == '%')
    process_format(out);
  else
    out << ch;
}
