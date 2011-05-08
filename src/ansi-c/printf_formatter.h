/*******************************************************************\

Module: printf Formatting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PRINTF_FORMATTER
#define CPROVER_PRINTF_FORMATTER

#include <expr.h>
#include <namespace.h>

class printf_formattert
{
public:
  void operator()(
    const std::string &format,
    const std::list<exprt> &_operands);

  void print(std::ostream &out);
  std::string as_string();
  
  explicit printf_formattert(const namespacet &_ns):ns(_ns)
  {
  }

protected:
  const namespacet &ns;
  std::string format;
  std::list<exprt> operands;
  std::list<exprt>::const_iterator next_operand;
  unsigned format_pos;
  inline bool eol() const { return format_pos>=format.size(); }
  
  class eol_exception { };

  char next()
  {
    if(eol()) throw eol_exception();
    return format[format_pos++];
  }
  
  void process_char(std::ostream &out);
  void process_format(std::ostream &out);

  const exprt make_type(const exprt &src, const typet &dest);
};

#endif
