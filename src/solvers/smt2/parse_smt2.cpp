/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cctype>
#include <stack>

#include "parse_smt2.h"

/*******************************************************************\

Function: get_simple_symbol()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#include <iostream>

std::string get_simple_symbol(char first, std::istream &in)
{
  // any non-empty sequence of letters, digits and the characters
  // ~ ! @ $ % ^ & * _ - + = < > . ? /
  // that does not start with a digit and is not a reserved word.

  std::string result;
  result+=first;

  char ch;
  while(in.get(ch))
  {
    if(isalnum(ch) || 
       ch=='~' || ch=='!' || ch=='@' || ch=='$' || ch=='%' ||
       ch=='^' || ch=='&' || ch=='*' || ch=='_' || ch=='-' ||
       ch=='+' || ch=='=' || ch=='<' || ch=='>' || ch=='.' ||
       ch=='?' || ch=='/')
      result+=ch;
    else
    {
      in.unget(); // put back
      return result;
    }
  }
  
  // eof is just ok here
  return result;
}

/*******************************************************************\

Function: get_quoted_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string get_quoted_symbol(std::istream &in)
{
  // any sequence of printable ASCII characters (including space,
  // tab, and line-breaking characters) except for the backslash
  // character \, that starts and ends with | and does not otherwise
  // contain |

  std::string result;
  
  char ch;
  while(in.get(ch))
  {
    if(ch=='|') return result;
    result+=ch;
  }

  // Hmpf. Eof before end of quoted string.  
  return result;
}

/*******************************************************************\

Function: get_string_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string get_string_literal(std::istream &in)
{
  // any sequence of printable ASCII characters delimited by
  // double quotes (") and possibly containing the C-style escape
  // sequences \" and double-backslash
  
  std::string result;
  
  char ch;
  while(in.get(ch))
  {
    if(ch=='"') return result;
    if(ch=='\\') in.get(ch); // quote
    result+=ch;
  }

  // Hmpf. Eof before end of string literal.
  return result;
}

/*******************************************************************\

Function: parse_smt2

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irept parse_smt2(std::istream &in)
{
  std::stack<irept> stack;
  char ch;

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
      // produce sub-irep
      stack.push(irept());
      break;
      
    case ')':
      {
        // done with sub-irep
        if(stack.empty()) return irept(); // unexpected )
        irept tmp=stack.top();
        stack.pop();

        if(stack.empty())
          return tmp;
        else
          stack.top().get_sub().push_back(tmp);
      }
      break;
      
    case '|': // quoted symbol
      {
        irep_idt symbol=get_quoted_symbol(in);

        if(stack.empty())
          return irept(symbol);
        else
          stack.top().get_sub().push_back(irept(symbol));
      }
      break;
      
    case '"': // string literal
      {
        irep_idt literal=get_string_literal(in);

        if(stack.empty())
          return irept(literal);
        else
          stack.top().get_sub().push_back(irept(literal));
      }

    default: // likely a simple symbol
      {
        irep_idt symbol=get_simple_symbol(ch, in);

        if(stack.empty())
          return irept(symbol);
        else
          stack.top().get_sub().push_back(irept(symbol));
      }
    }
  }
  
  // Hmpf, eof before we got anything
  return irept();
}
