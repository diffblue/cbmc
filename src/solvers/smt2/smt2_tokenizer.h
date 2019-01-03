/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SMT2_SMT2_TOKENIZER_H
#define CPROVER_SOLVERS_SMT2_SMT2_TOKENIZER_H

#include <util/exception_utils.h>

#include <sstream>
#include <string>

class smt2_tokenizert
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
      : line_no(_line_no)
    {
      message << _message;
    }

    explicit smt2_errort(unsigned _line_no) : line_no(_line_no)
    {
    }

    std::string what() const override
    {
      return message.str();
    }

    unsigned get_line_no() const
    {
      return line_no;
    }

    std::ostringstream &message_ostream()
    {
      return message;
    }

  protected:
    std::ostringstream message;
    unsigned line_no;
  };

  using tokent = enum {
    NONE,
    END_OF_FILE,
    STRING_LITERAL,
    NUMERAL,
    SYMBOL,
    KEYWORD,
    OPEN,
    CLOSE
  };

  tokent next_token();

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

  const std::string &get_buffer() const
  {
    return buffer;
  }

  bool token_is_quoted_symbol() const
  {
    return quoted_symbol;
  }

  /// generate an error exception, pre-filled with a message
  smt2_errort error(const std::string &message)
  {
    return smt2_errort(message, line_no);
  }

  /// generate an error exception
  smt2_errort error()
  {
    return smt2_errort(line_no);
  }

protected:
  std::istream *in;
  unsigned line_no;
  std::string buffer;
  bool quoted_symbol = false;
  bool peeked;
  tokent token;

  /// skip any tokens until all parentheses are closed
  /// or the end of file is reached
  void skip_to_end_of_list();

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

/// add to the diagnostic information in the given smt2_tokenizer exception
template <typename T>
smt2_tokenizert::smt2_errort
operator<<(smt2_tokenizert::smt2_errort &&e, const T &message)
{
  e.message_ostream() << message;
  return std::move(e);
}

#endif // CPROVER_SOLVERS_SMT2_SMT2_PARSER_H
