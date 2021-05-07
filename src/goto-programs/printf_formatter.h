/*******************************************************************\

Module: printf Formatting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// printf Formatting

#ifndef CPROVER_GOTO_PROGRAMS_PRINTF_FORMATTER_H
#define CPROVER_GOTO_PROGRAMS_PRINTF_FORMATTER_H

#include <util/expr.h>

#include <list>

class printf_formattert
{
public:
  void operator()(
    const std::string &format,
    const std::list<exprt> &_operands);

  void print(std::ostream &out);
  std::string as_string();

  explicit printf_formattert(const namespacet &_ns):
    ns(_ns),
    format_pos(0)
  {
  }

protected:
  const namespacet &ns;
  std::string format;
  std::list<exprt> operands;
  std::list<exprt>::const_iterator next_operand;
  unsigned format_pos;
  bool eol() const { return format_pos>=format.size(); }

  class eol_exceptiont { };

  char next()
  {
    if(eol())
      throw eol_exceptiont();
    return format[format_pos++];
  }

  void process_char(std::ostream &out);
  void process_format(std::ostream &out);

  const exprt make_type(const exprt &src, const typet &dest);
};

#endif // CPROVER_GOTO_PROGRAMS_PRINTF_FORMATTER_H
