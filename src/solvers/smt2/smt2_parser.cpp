/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <istream>
#include <ostream>

#include "smt2_parser.h"

/*******************************************************************\

Function: smt2_parsert::is_simple_symbol_character

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool smt2_parsert::is_simple_symbol_character(char ch)
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

/*******************************************************************\

Function: smt2_parsert::get_simple_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_parsert::get_simple_symbol()
{
  // any non-empty sequence of letters, digits and the characters
  // ~ ! @ $ % ^ & * _ - + = < > . ? /
  // that does not start with a digit and is not a reserved word.

  buffer.clear();

  char ch;
  while(in.get(ch))
  {
    if(is_simple_symbol_character(ch))
    {
      buffer+=ch;
    }
    else
    {
      in.unget(); // put back
      return;
    }
  }
  
  // eof -- this is ok here
}

/*******************************************************************\

Function: smt2_parsert::get_decimal_numeral

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_parsert::get_decimal_numeral()
{
  // we accept any sequence of digits and dots

  buffer.clear();

  char ch;
  while(in.get(ch))
  {
    if(isdigit(ch) || ch=='.')
    {
      buffer+=ch;
    }
    else
    {
      in.unget(); // put back
      return;
    }
  }
  
  // eof -- this is ok here
}

/*******************************************************************\

Function: smt2_parsert::get_bin_numeral

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_parsert::get_bin_numeral()
{
  // we accept any sequence of '0' or '1'

  buffer.clear();
  buffer+='#';
  buffer+='b';

  char ch;
  while(in.get(ch))
  {
    if(ch=='0' || ch=='1')
    {
      buffer+=ch;
    }
    else
    {
      in.unget(); // put back
      return;
    }
  }
  
  // eof -- this is ok here
}

/*******************************************************************\

Function: smt2_parsert::get_hex_numeral

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_parsert::get_hex_numeral()
{
  // we accept any sequence of '0'-'9', 'a'-'f', 'A'-'F'

  buffer.clear();
  buffer+='#';
  buffer+='x';

  char ch;
  while(in.get(ch))
  {
    if(isxdigit(ch))
    {
      buffer+=ch;
    }
    else
    {
      in.unget(); // put back
      return;
    }
  }
  
  // eof -- this is ok here
}

/*******************************************************************\

Function: smt2_parsert::get_quoted_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_parsert::get_quoted_symbol()
{
  // any sequence of printable ASCII characters (including space,
  // tab, and line-breaking characters) except for the backslash
  // character \, that starts and ends with | and does not otherwise
  // contain |

  buffer.clear();
  
  char ch;
  while(in.get(ch))
  {
    if(ch=='|') return; // done
    buffer+=ch;
  }

  // Hmpf. Eof before end of quoted string. This is an error.
}

/*******************************************************************\

Function: smt2_parsert::get_string_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_parsert::get_string_literal()
{
  buffer.clear();
  
  char ch;
  while(in.get(ch))
  {
    if(ch=='"')
    {
      // quotes may be escaped by repeating
      if(in.get(ch))
      {
        if(ch=='"')
        {
        }
        else
        {
          in.unget();
          return; // done 
        }
      }
      else
        return; // done
    }
    buffer+=ch;
  }

  // Hmpf. Eof before end of string literal. This is an error.
  error("EOF within string literal");
}

/*******************************************************************\

Function: smt2_parsert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_parsert::operator()()
{
  char ch;
  unsigned open_parentheses=0;

  while(in.get(ch))
  {
    switch(ch)
    {
    case ' ':
    case '\n':
    case '\r':
    case '\t':
    case (char)160: // non-breaking space
      // skip any whitespace
      break;
    
    case ';': // comment
      // skip until newline
      while(in.get(ch) && ch!='\n')
        ; // ignore
      break;
    
    case '(':
      // produce sub-expression
      open_parentheses++;
      open_expression();
      break;
      
    case ')':
      // done with sub-expression
      if(open_parentheses==0) // unexpected ')'. This is an error.
      {
        error("unexpected closing parenthesis");
        return;
      }
      
      open_parentheses--;

      close_expression();
      
      if(open_parentheses==0)
        return; // done        

      break;
      
    case '|': // quoted symbol
      get_quoted_symbol();
      symbol();
      if(open_parentheses==0) return; // done
      break;
      
    case '"': // string literal
      get_string_literal();
      string_literal();
      if(open_parentheses==0) return; // done
      break;
      
    case ':': // keyword
      get_simple_symbol();
      keyword();
      if(open_parentheses==0) return; // done
      break;
      
    case '#':
      if(in.get(ch))
      {
        if(ch=='b')
        {
          get_bin_numeral();
          numeral();
        }
        else if(ch=='x')
        {
          get_hex_numeral();
          numeral();
        }
        else
        {
          error("unexpected numeral token");
          return;
        }
         
        if(open_parentheses==0) return; // done
      }
      else
      {
        error("unexpected EOF in numeral token");
        return;
      }
      break;

    default: // likely a simple symbol or a numeral
      if(isdigit(ch))
      {
        in.unget();
        get_decimal_numeral();
        numeral();
        if(open_parentheses==0) return; // done
      }
      else if(is_simple_symbol_character(ch))
      {
        in.unget();
        get_simple_symbol();
        symbol();
        if(open_parentheses==0) return; // done
      }
      else
      {
        // illegal character, error
        error("unexpected character");
        return;
      }
    }
  }

  if(open_parentheses==0)
  {  
    // Hmpf, eof before we got anything. Blank file!
  }
  else
  {
    // Eof before end of expression. Error!
    error("EOF before end of expression");
  }
}
