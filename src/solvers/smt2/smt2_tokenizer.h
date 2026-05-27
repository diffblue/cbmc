/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Tokenizer for the SMT-LIB v2.6 syntax.  Splits an input stream into
/// a sequence of \ref smt2_tokenizert::tokent values that the parser
/// consumes via \ref smt2_tokenizert::next_token and
/// \ref smt2_tokenizert::peek.

#ifndef CPROVER_SOLVERS_SMT2_SMT2_TOKENIZER_H
#define CPROVER_SOLVERS_SMT2_SMT2_TOKENIZER_H

#include <optional>
#include <sstream>
#include <string>

class smt2_tokenizert
{
public:
  explicit smt2_tokenizert(std::istream &_in) : in(&_in)
  {
  }

  /// Exception thrown by the tokenizer (and the parser built on top of
  /// it) to report a syntactic error at a known source line.  Holds an
  /// `std::ostringstream` so that callers can assemble the diagnostic
  /// piecewise via `operator<<`.
  class smt2_errort
  {
  public:
    smt2_errort(smt2_errort &&) = default;

    smt2_errort(const smt2_errort &other)
    {
      // ostringstream does not have a copy constructor
      message << other.message.str();
      line_no = other.line_no;
    }

    smt2_errort(const std::string &_message, unsigned _line_no)
      : line_no(_line_no)
    {
      message << _message;
    }

    explicit smt2_errort(unsigned _line_no) : line_no(_line_no)
    {
    }

    std::string what() const
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

  using token_kindt = enum {
    NONE,
    END_OF_FILE,
    STRING_LITERAL,
    NUMERAL,
    SYMBOL,
    KEYWORD,
    OPEN,
    CLOSE
  };

  /// One SMT-LIB v2.6 token.  Pure value class: it carries the token
  /// kind, the source text, the line number on which the token ends,
  /// and -- for SYMBOL only -- whether the symbol was supplied in
  /// `|...|` quoted form.  It does not hold any tokenizer state.
  class tokent
  {
  public:
    tokent() = default;
    explicit tokent(token_kindt _kind) : kind(_kind)
    {
    }

    /// The kind of token; see \ref token_kindt.
    token_kindt kind = NONE;
    /// The source text of the token (excluding any delimiters):
    /// the symbol name for SYMBOL/KEYWORD, the digits/`#b`/`#x`
    /// representation for NUMERAL, the unescaped contents of a
    /// STRING_LITERAL, empty for OPEN/CLOSE/END_OF_FILE.
    std::string text;
    /// The source line number on which the token ends.
    unsigned line_no = 0;
    /// True iff `kind == SYMBOL` and the symbol was given in `|...|`
    /// quoted form; always false for other token kinds.
    bool quoted_symbol = false;

    /// Implicit conversion to the kind so the parser can keep using
    /// `switch(token)` and `token == OPEN` patterns directly.
    operator token_kindt() const
    {
      return kind;
    }
  };

  /// Consume and return the next token.  If a token has been peeked
  /// (see \ref peek) it is returned; otherwise the next token is read
  /// from the input stream.
  tokent next_token();

  /// Return the next token without consuming it.  A subsequent call
  /// to \ref next_token will return the same token.  Repeated calls
  /// to \ref peek return the same token without re-reading from the
  /// stream.
  const tokent &peek()
  {
    if(!peeked.has_value())
      peeked = read_token();
    return *peeked;
  }

  /// generate an error exception, pre-filled with a message
  smt2_errort error(const std::string &message) const
  {
    return smt2_errort(message, current_line_no());
  }

  /// generate an error exception
  smt2_errort error() const
  {
    return smt2_errort(current_line_no());
  }

protected:
  std::istream *in;

  /// skip any tokens until all parentheses are closed
  /// or the end of file is reached
  void skip_to_end_of_list();

private:
  /// Number of the source line currently being read.  Is incremented as
  /// `\n` characters are consumed from the input stream and then stamped
  /// onto each tokent emitted by the helpers below.
  unsigned line_no = 1;

  /// Token that has been peeked but not yet consumed.
  std::optional<tokent> peeked;

  /// Line number to attribute a diagnostic to: the line of the peeked
  /// token if there is one, otherwise the current input line.
  unsigned current_line_no() const
  {
    return peeked.has_value() ? peeked->line_no : line_no;
  }

  /// Read a NUMERAL of the form "[0-9.]+" from the stream.  Called
  /// after the leading digit has been seen and unget'd back onto the
  /// stream.
  tokent get_decimal_numeral();
  /// Read a NUMERAL of the form "#x[0-9a-fA-F]+" from the stream.
  /// Called after the leading `#x` has been consumed.
  tokent get_hex_numeral();
  /// Read a NUMERAL of the form "#b[01]+" from the stream.  Called
  /// after the leading `#b` has been consumed.
  tokent get_bin_numeral();
  /// Read a SYMBOL of the form "[A-Za-z~!@$%^&*_\-+=<>.?/][...]*"
  /// from the stream.  Called after the leading character has been
  /// seen and unget'd back onto the stream.  Returns an END_OF_FILE
  /// token if the stream is at end-of-file with an empty buffer.
  tokent get_simple_symbol();
  /// Read a quoted SYMBOL of the form `|...|` from the stream.  Called
  /// after the opening `|` has been consumed.  Throws \ref smt2_errort
  /// if EOF is reached before the closing `|`.  Newlines inside
  /// `|...|` are legal and increment \ref line_no.
  tokent get_quoted_symbol();
  /// Read a STRING_LITERAL of the form `"..."` from the stream,
  /// applying SMT-LIB v2.6 quote-doubling: a `""` inside the literal
  /// is interpreted as a single `"`.  Called after the opening `"`
  /// has been consumed.  Throws \ref smt2_errort if EOF is reached
  /// before the closing `"`.
  tokent get_string_literal();

  /// Read a single token directly from the input stream.  Does not
  /// consult or update `peeked` -- callers handle that.
  tokent read_token();
};

/// add to the diagnostic information in the given smt2_tokenizer exception
template <typename T>
smt2_tokenizert::smt2_errort
operator<<(smt2_tokenizert::smt2_errort &&e, const T &message)
{
  e.message_ostream() << message;
  return std::move(e);
}

bool is_smt2_simple_symbol_character(char);

#endif // CPROVER_SOLVERS_SMT2_SMT2_PARSER_H
