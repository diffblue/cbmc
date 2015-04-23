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
  
  // string literal, numeral, simple symbol, quoted symbol
  // and keyword are in 'buffer'
  virtual void string_literal() = 0;
  virtual void numeral() = 0;
  virtual void symbol() = 0;
  virtual void keyword() = 0;
  virtual void open_expression() = 0; // '('
  virtual void close_expression() = 0; // ')'

  // parse errors
  virtual void error(const std::string &) = 0;

private:
  void get_decimal_numeral();
  void get_hex_numeral();
  void get_bin_numeral();
  void get_simple_symbol();
  void get_quoted_symbol();
  void get_string_literal();
  bool is_simple_symbol_character(char ch);
};

