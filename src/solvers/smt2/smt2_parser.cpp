/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <istream>
#include <ostream>

#include "smt2_parser.h"

/*******************************************************************\

Function: smt2_parsert::get_simple_symbol()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_parsert::get_simple_symbol(char first)
{
  // any non-empty sequence of letters, digits and the characters
  // ~ ! @ $ % ^ & * _ - + = < > . ? /
  // that does not start with a digit and is not a reserved word.

  buffer.clear();
  buffer+=first;

  char ch;
  while(in.get(ch))
  {
    if(isalnum(ch) || 
       ch=='~' || ch=='!' || ch=='@' || ch=='$' || ch=='%' ||
       ch=='^' || ch=='&' || ch=='*' || ch=='_' || ch=='-' ||
       ch=='+' || ch=='=' || ch=='<' || ch=='>' || ch=='.' ||
       ch=='?' || ch=='/')
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
  // any sequence of printable ASCII characters delimited by
  // double quotes (") and possibly containing the C-style escape
  // sequences \" and double-backslash

  buffer.clear();
  
  char ch;
  while(in.get(ch))
  {
    if(ch=='"') return; // done 
    if(ch=='\\') in.get(ch); // quote
    buffer+=ch;
  }

  // Hmpf. Eof before end of string literal. This is an error.
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
      if(open_parentheses==0) // unexpected ')'. This is an error;
        return;
      
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
      symbol();
      if(open_parentheses==0) return; // done
      break;

    default: // likely a simple symbol
      get_simple_symbol(ch);
      symbol();
      if(open_parentheses==0) return; // done
    }
  }

  if(open_parentheses==0)
  {  
    // Hmpf, eof before we got anything. Blank file!
  }
  else
  {
    // Eof before end of expression. Error!
  }
}

/*******************************************************************\

Function: smt2_parser_test

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class smt2_parser_testt:public smt2_parsert
{
public:
  smt2_parser_testt(std::istream &_in, std::ostream &_out):
    smt2_parsert(_in), out(_out), first(true)
  {
  }
  
protected:
  std::ostream &out;
  bool first;

  // overload from smt2_parsert

  virtual void symbol()
  {
    if(first)
      first=false;
    else
      out << ' ';

    out << buffer;
  }
  
  virtual void open_expression() // '('
  {
    if(!first)
      out << ' ';
      
    out << '(';
    first=true;
  }
  
  virtual void close_expression() // ')'
  {
    out << ')';
  }
};

void smt2_parser_test(std::istream &in, std::ostream &out)
{
  smt2_parser_testt(in, out)();
}
