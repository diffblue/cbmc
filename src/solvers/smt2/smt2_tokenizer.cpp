/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Implementation of the SMT-LIB v2.6 tokenizer; see
/// `smt2_tokenizer.h` for the corresponding interface.

#include "smt2_tokenizer.h"

bool is_smt2_simple_symbol_character(char ch)
{
  // any non-empty sequence of letters, digits and the characters
  // ~ ! @ $ % ^ & * _ - + = < > . ? /
  // that does not start with a digit and is not a reserved word.

  return isalnum(ch) ||
     ch=='~' || ch=='!' || ch=='@' || ch=='$' || ch=='%' ||
     ch=='^' || ch=='&' || ch=='*' || ch=='_' || ch=='-' ||
     ch=='+' || ch=='=' || ch=='<' || ch=='>' || ch=='.' ||
     ch=='?' || ch=='/';
}

smt2_tokenizert::tokent smt2_tokenizert::get_simple_symbol()
{
  // any non-empty sequence of letters, digits and the characters
  // ~ ! @ $ % ^ & * _ - + = < > . ? /
  // that does not start with a digit and is not a reserved word.

  tokent t{SYMBOL};

  char ch;
  while(in->get(ch))
  {
    if(is_smt2_simple_symbol_character(ch))
    {
      t.text += ch;
    }
    else
    {
      in->unget(); // put back
      t.line_no = line_no;
      return t;
    }
  }

  // eof -- this is ok here
  t.line_no = line_no;
  if(t.text.empty())
    t.kind = END_OF_FILE;
  return t;
}

smt2_tokenizert::tokent smt2_tokenizert::get_decimal_numeral()
{
  // we accept any sequence of digits and dots

  tokent t{NUMERAL};

  char ch;
  while(in->get(ch))
  {
    if(isdigit(ch) || ch=='.')
    {
      t.text += ch;
    }
    else
    {
      in->unget(); // put back
      t.line_no = line_no;
      return t;
    }
  }

  // eof -- this is ok here
  t.line_no = line_no;
  if(t.text.empty())
    t.kind = END_OF_FILE;
  return t;
}

smt2_tokenizert::tokent smt2_tokenizert::get_bin_numeral()
{
  // we accept any sequence of '0' or '1'

  tokent t{NUMERAL};
  t.text = "#b";

  char ch;
  while(in->get(ch))
  {
    if(ch=='0' || ch=='1')
    {
      t.text += ch;
    }
    else
    {
      in->unget(); // put back
      t.line_no = line_no;
      return t;
    }
  }

  // eof -- this is ok here
  t.line_no = line_no;
  return t;
}

smt2_tokenizert::tokent smt2_tokenizert::get_hex_numeral()
{
  // we accept any sequence of '0'-'9', 'a'-'f', 'A'-'F'

  tokent t{NUMERAL};
  t.text = "#x";

  char ch;
  while(in->get(ch))
  {
    if(isxdigit(ch))
    {
      t.text += ch;
    }
    else
    {
      in->unget(); // put back
      t.line_no = line_no;
      return t;
    }
  }

  // eof -- this is ok here
  t.line_no = line_no;
  return t;
}

smt2_tokenizert::tokent smt2_tokenizert::get_quoted_symbol()
{
  // any sequence of printable ASCII characters (including space,
  // tab, and line-breaking characters) except for the backslash
  // character \, that starts and ends with | and does not otherwise
  // contain |

  tokent t{SYMBOL};
  t.quoted_symbol = true;

  char ch;
  while(in->get(ch))
  {
    if(ch=='|')
    {
      t.line_no = line_no;
      return t;
    }

    t.text += ch;

    if(ch=='\n')
      line_no++;
  }

  // Hmpf. Eof before end of quoted symbol. This is an error.
  throw error("EOF within quoted symbol");
}

smt2_tokenizert::tokent smt2_tokenizert::get_string_literal()
{
  tokent t{STRING_LITERAL};

  char ch;
  while(in->get(ch))
  {
    if(ch=='"')
    {
      // quotes may be escaped by repeating
      if(in->get(ch))
      {
        if(ch=='"')
        {
        }
        else
        {
          in->unget();
          t.line_no = line_no;
          return t; // done
        }
      }
      else
      {
        t.line_no = line_no;
        return t; // done
      }
    }
    t.text += ch;
  }

  // Hmpf. Eof before end of string literal. This is an error.
  throw error("EOF within string literal");
}

smt2_tokenizert::tokent smt2_tokenizert::next_token()
{
  if(peeked.has_value())
  {
    tokent result = std::move(*peeked);
    peeked.reset();
    return result;
  }
  return read_token();
}

smt2_tokenizert::tokent smt2_tokenizert::read_token()
{
  char ch;

  while(in->get(ch))
  {
    switch(ch)
    {
    case '\n':
      line_no++;
      break;

    case ' ':
    case '\r':
    case '\t':
    case static_cast<char>(160): // non-breaking space
      // skip any whitespace
      break;

    case ';': // comment
      // skip until newline
      while(in->get(ch))
      {
        if(ch=='\n')
        {
          line_no++;
          break;
        }
      }
      break;

    case '(':
    {
      tokent t{OPEN};
      t.line_no = line_no;
      return t;
    }

    case ')':
    {
      tokent t{CLOSE};
      t.line_no = line_no;
      return t;
    }

    case '|': // quoted symbol
      return get_quoted_symbol();

    case '"': // string literal
      return get_string_literal();

    case ':': // keyword
    {
      tokent t = get_simple_symbol();
      if(t.kind != SYMBOL)
        throw error("expecting symbol after colon");
      t.kind = KEYWORD;
      return t;
    }

    case '#':
      if(in->get(ch))
      {
        if(ch=='b')
          return get_bin_numeral();
        else if(ch=='x')
          return get_hex_numeral();
        else
          throw error("unknown numeral token");
      }
      else
        throw error("unexpected EOF in numeral token");
      break;

    default: // likely a simple symbol or a numeral
      if(isdigit(ch))
      {
        in->unget();
        return get_decimal_numeral();
      }
      else if(is_smt2_simple_symbol_character(ch))
      {
        in->unget();
        return get_simple_symbol();
      }
      else
      {
        // illegal character, error
        throw error() << "unexpected character '" << ch << '\'';
      }
    }
  }

  tokent t{END_OF_FILE};
  t.line_no = line_no;
  return t;
}
