/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iosfwd>
#include <string>

class smt2_parsert
{
public:
  smt2_parsert(std::istream &_in):in(_in)
  {
  }
  
  void operator()();
  
protected:
  std::istream &in;
  std::string buffer;
  
  // string literal, simple symbol, quoted symbol in buffer
  virtual void string_literal() = 0;
  virtual void symbol() = 0;
  virtual void open_expression() = 0; // '('
  virtual void close_expression() = 0; // ')'

private:
  void get_simple_symbol(char first);
  void get_quoted_symbol();
  void get_string_literal();
};

