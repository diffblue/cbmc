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
  error() << "EOF within quoted symbol" << eom;
  return ERROR;
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
  error() << "EOF within string literal" << eom;
  return ERROR;
}

smt2_tokenizert::tokent smt2_tokenizert::next_token()
{
  if(peeked)
    return peeked=false, token;

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
      return token=OPEN;

    case ')':
      // done with sub-expression
      return token=CLOSE;

    case '|': // quoted symbol
      return token=get_quoted_symbol();

    case '"': // string literal
      return token=get_string_literal();

    case ':': // keyword
      return token=get_simple_symbol();

    case '#':
      if(in->get(ch))
      {
        if(ch=='b')
          return token=get_bin_numeral();
        else if(ch=='x')
          return token=get_hex_numeral();
        else
        {
          error() << "unknown numeral token" << eom;
          return token=ERROR;
        }
      }
      else
      {
        error() << "unexpected EOF in numeral token" << eom;
        return token=ERROR;
      }
      break;

    default: // likely a simple symbol or a numeral
      if(isdigit(ch))
      {
        in->unget();
        return token=get_decimal_numeral();
      }
      else if(is_simple_symbol_character(ch))
      {
        in->unget();
        return token=get_simple_symbol();
      }
      else
      {
        // illegal character, error
        error() << "unexpected character `" << ch << '\'' << eom;
        return token=ERROR;
      }
    }
  }

  return token=END_OF_FILE;
}
