/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2_tokenizer.h"

#include <istream>

bool smt2_tokenizert::is_simple_symbol_character(char ch)
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

  buffer.clear();

  char ch;
  while(in->get(ch))
  {
    if(is_simple_symbol_character(ch))
    {
      buffer+=ch;
    }
    else
    {
      in->unget(); // put back
      return SYMBOL;
    }
  }

  // eof -- this is ok here
  if(buffer.empty())
    return END_OF_FILE;
  else
    return SYMBOL;
}

smt2_tokenizert::tokent smt2_tokenizert::get_decimal_numeral()
{
  // we accept any sequence of digits and dots

  buffer.clear();

  char ch;
  while(in->get(ch))
  {
    if(isdigit(ch) || ch=='.')
    {
      buffer+=ch;
    }
    else
    {
      in->unget(); // put back
      return NUMERAL;
    }
  }

  // eof -- this is ok here
  if(buffer.empty())
    return END_OF_FILE;
  else
    return NUMERAL;
}

smt2_tokenizert::tokent smt2_tokenizert::get_bin_numeral()
{
  // we accept any sequence of '0' or '1'

  buffer.clear();
  buffer+='#';
  buffer+='b';

  char ch;
  while(in->get(ch))
  {
    if(ch=='0' || ch=='1')
    {
      buffer+=ch;
    }
    else
    {
      in->unget(); // put back
      return NUMERAL;
    }
  }

  // eof -- this is ok here
  if(buffer.empty())
    return END_OF_FILE;
  else
    return NUMERAL;
}

smt2_tokenizert::tokent smt2_tokenizert::get_hex_numeral()
{
  // we accept any sequence of '0'-'9', 'a'-'f', 'A'-'F'

  buffer.clear();
  buffer+='#';
  buffer+='x';

  char ch;
  while(in->get(ch))
  {
    if(isxdigit(ch))
    {
      buffer+=ch;
    }
    else
    {
      in->unget(); // put back
      return NUMERAL;
    }
  }

  // eof -- this is ok here
  if(buffer.empty())
    return END_OF_FILE;
  else
    return NUMERAL;
}

smt2_tokenizert::tokent smt2_tokenizert::get_quoted_symbol()
{
  // any sequence of printable ASCII characters (including space,
  // tab, and line-breaking characters) except for the backslash
  // character \, that starts and ends with | and does not otherwise
  // contain |

  buffer.clear();

  char ch;
  while(in->get(ch))
  {
    if(ch=='|')
      return SYMBOL; // done

    buffer+=ch;

    if(ch=='\n')
      line_no++;
  }

  // Hmpf. Eof before end of quoted symbol. This is an error.
  throw error("EOF within quoted symbol");
}

smt2_tokenizert::tokent smt2_tokenizert::get_string_literal()
{
  buffer.clear();

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
          return STRING_LITERAL; // done
        }
      }
      else
        return STRING_LITERAL; // done
    }
    buffer+=ch;
  }

  // Hmpf. Eof before end of string literal. This is an error.
  throw error("EOF within string literal");
}

smt2_tokenizert::tokent smt2_tokenizert::next_token()
{
  if(peeked)
    peeked = false;
  else
    get_token_from_stream();

  return token;
}

void smt2_tokenizert::get_token_from_stream()
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
      // produce sub-expression
      token = OPEN;
      return;

    case ')':
      // done with sub-expression
      token = CLOSE;
      return;

    case '|': // quoted symbol
      token = get_quoted_symbol();
      return;

    case '"': // string literal
      token = get_string_literal();
      return;

    case ':': // keyword
      token = get_simple_symbol();
      return;

    case '#':
      if(in->get(ch))
      {
        if(ch=='b')
        {
          token = get_bin_numeral();
          return;
        }
        else if(ch=='x')
        {
          token = get_hex_numeral();
          return;
        }
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
        token = get_decimal_numeral();
        return;
      }
      else if(is_simple_symbol_character(ch))
      {
        in->unget();
        token = get_simple_symbol();
        return;
      }
      else
      {
        // illegal character, error
        std::ostringstream msg;
        msg << "unexpected character `" << ch << '\'';
        throw error(msg.str());
      }
    }
  }

  token = END_OF_FILE;
}
