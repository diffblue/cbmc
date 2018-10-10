/*******************************************************************\

Module: printf Formatting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// printf Formatting

#include "printf_formatter.h"

#include <cassert>
#include <sstream>

#include <util/c_types.h>
#include <util/format_constant.h>
#include <util/simplify_expr.h>

const exprt printf_formattert::make_type(
  const exprt &src, const typet &dest)
{
  if(src.type()==dest)
    return src;
  exprt tmp=src;
  tmp.make_typecast(dest);
  simplify(tmp, ns);
  return tmp;
}

void printf_formattert::operator()(
  const std::string &_format,
  const std::list<exprt> &_operands)
{
  format=_format;
  operands=_operands;
}

void printf_formattert::print(std::ostream &out)
{
  format_pos=0;
  next_operand=operands.begin();

  try
  {
    while(!eol()) process_char(out);
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

  format_constant.precision=6;
  format_constant.min_width=0;
  format_constant.zero_padding=false;

  char ch=next();

  if(ch=='0') // leading zeros
  {
    format_constant.zero_padding=true;
    ch=next();
  }

  while(isdigit(ch)) // width
  {
    format_constant.min_width*=10;
    format_constant.min_width+=ch-'0';
    ch=next();
  }

  if(ch=='.') // precision
  {
    format_constant.precision=0;
    ch=next();

    while(isdigit(ch))
    {
      format_constant.precision*=10;
      format_constant.precision+=ch-'0';
      ch=next();
    }
  }

  switch(ch)
  {
  case '%':
    out << ch;
    break;

  case 'e':
  case 'E':
    format_constant.style=format_spect::stylet::SCIENTIFIC;
    if(next_operand==operands.end())
      break;
    out << format_constant(
      make_type(*(next_operand++), double_type()));
    break;

  case 'f':
  case 'F':
    format_constant.style=format_spect::stylet::DECIMAL;
    if(next_operand==operands.end())
      break;
    out << format_constant(
      make_type(*(next_operand++), double_type()));
    break;

  case 'g':
  case 'G':
    format_constant.style=format_spect::stylet::AUTOMATIC;
    if(format_constant.precision==0)
      format_constant.precision=1;
    if(next_operand==operands.end())
      break;
    out << format_constant(
      make_type(*(next_operand++), double_type()));
    break;

  case 's':
    {
      if(next_operand==operands.end())
        break;
      // this is the address of a string
      const exprt &op=*(next_operand++);
      if(op.id()==ID_address_of &&
         op.operands().size()==1 &&
         op.op0().id()==ID_index &&
         op.op0().operands().size()==2 &&
         op.op0().op0().id()==ID_string_constant)
        out << format_constant(op.op0().op0());
    }
    break;

  case 'd':
    if(next_operand==operands.end())
      break;
    out << format_constant(
      make_type(*(next_operand++), signed_int_type()));
    break;

  case 'D':
    if(next_operand==operands.end())
      break;
    out << format_constant(
      make_type(*(next_operand++), signed_long_int_type()));
    break;

  case 'u':
    if(next_operand==operands.end())
      break;
    out << format_constant(
      make_type(*(next_operand++), unsigned_int_type()));
    break;

  case 'U':
    if(next_operand==operands.end())
      break;
    out << format_constant(
      make_type(*(next_operand++), unsigned_long_int_type()));
    break;

  default:
    out << '%' << ch;
  }
}

void printf_formattert::process_char(std::ostream &out)
{
  char ch=next();

  if(ch=='%')
    process_format(out);
  else
    out << ch;
}
