/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SMT2_SMT2_TOKENIZER_H
#define CPROVER_SOLVERS_SMT2_SMT2_TOKENIZER_H

#include <util/exception_utils.h>
#include <util/parser.h>

#include <string>

class smt2_tokenizert:public parsert
{
public:
  explicit smt2_tokenizert(std::istream &_in) : peeked(false), token(NONE)
  {
    in=&_in;
    line_no=1;
  }

  class smt2_errort : public cprover_exception_baset
  {
  public:
    smt2_errort(const std::string &_message, unsigned _line_no)
      : message(_message), line_no(_line_no)
    {
    }

    smt2_errort(std::string &&_message, unsigned _line_no)
      : message(std::move(_message)), line_no(_line_no)
    {
    }

    std::string what() const override
    {
      return message;
    }

    unsigned get_line_no() const
    {
      return line_no;
    }

  protected:
    const std::string message;
    unsigned line_no;
  };

protected:
  std::string buffer;
  bool peeked;
  using tokent = enum {
    NONE,
    END_OF_FILE,
    STRING_LITERAL,
    NUMERAL,
    SYMBOL,
    OPEN,
    CLOSE
  };
  tokent token;

  virtual tokent next_token();

  tokent peek()
  {
    if(peeked)
      return token;
    else
    {
      get_token_from_stream();
      peeked=true;
      return token;
    }
  }

  /// skip any tokens until all parentheses are closed
  /// or the end of file is reached
  void skip_to_end_of_list();

  smt2_errort error(std::string &&message)
  {
    return smt2_errort(std::move(message), line_no);
  }

  smt2_errort error(const std::ostringstream &message)
  {
    return smt2_errort(message.str(), line_no);
  }

private:
  tokent get_decimal_numeral();
  tokent get_hex_numeral();
  tokent get_bin_numeral();
  tokent get_simple_symbol();
  tokent get_quoted_symbol();
  tokent get_string_literal();
  static bool is_simple_symbol_character(char);

  /// read a token from the input stream and store it in 'token'
  void get_token_from_stream();
};

#endif // CPROVER_SOLVERS_SMT2_SMT2_PARSER_H
