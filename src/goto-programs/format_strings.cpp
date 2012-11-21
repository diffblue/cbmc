/*******************************************************************\

Module: Format String Parser

Author: CM Wintersteiger

\*******************************************************************/

#include <ctype.h>

#include "format_strings.h"

/*******************************************************************\

Function: parse_flags

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void parse_flags(
  std::string::const_iterator &it,
  format_tokent &curtok)
{
  while(*it=='#' || *it=='0' ||
        *it=='-' || *it==' ' || *it=='+')
  {
    switch(*it)
    {
      case '#': curtok.flags.push_back(format_tokent::ALTERNATE); break;
      case '0': curtok.flags.push_back(format_tokent::ZERO_PAD); break;
      case '-': curtok.flags.push_back(format_tokent::LEFT_ADJUST); break;
      case ' ': curtok.flags.push_back(format_tokent::SIGNED_SPACE); break;
      case '+': curtok.flags.push_back(format_tokent::SIGN); break;
      default: throw 0;
    }
    it++;
  }
}

/*******************************************************************\

Function: parse_field_width

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void parse_field_width(
  std::string::const_iterator &it,
  format_tokent &curtok)
{
  if(*it=='*')
  {
    curtok.flags.push_back(format_tokent::ASTERISK);
    it++;
  }

  std::string tmp;
  for(;isdigit(*it); it++) tmp+=*it;
  curtok.field_width=string2integer(tmp);
}

/*******************************************************************\

Function: parse_precision

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void parse_precision(
  std::string::const_iterator &it,
  format_tokent &curtok)
{
  if(*it=='.')
  {
    it++;

    if(*it=='*')
    {
      curtok.flags.push_back(format_tokent::ASTERISK);
      it++;
    }
    else
    {
      std::string tmp;
      for(;isdigit(*it); it++) tmp+=*it;
      curtok.precision=string2integer(tmp);
    }
  }
}

/*******************************************************************\

Function: parse_length_modifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void parse_length_modifier(
  std::string::const_iterator &it,
  format_tokent &curtok)
{
  if(*it=='h')
  {
    it++;
    if(*it=='h') it++;
    curtok.length_modifier = format_tokent::LEN_h;
  }
  else if(*it=='l')
  {
    it++;
    if(*it=='l') it++;
    curtok.length_modifier = format_tokent::LEN_l;
  }
  else if(*it=='L')
  {
    it++;
    curtok.length_modifier = format_tokent::LEN_L;
  }
  else if(*it=='j')
  {
    it++;
    curtok.length_modifier = format_tokent::LEN_j;
  }
  else if(*it=='t')
  {
    it++;
    curtok.length_modifier = format_tokent::LEN_L;
  }
}

/*******************************************************************\

Function: parse_conversion_specifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void parse_conversion_specifier(
  const std::string &arg_string,
  std::string::const_iterator &it,
  format_tokent &curtok)
{
  switch(*it)
  {
    case 'd':
    case 'i': curtok.type=format_tokent::SIGNED_DEC; break;
    case 'o': curtok.type=format_tokent::UNSIGNED_OCT; break;
    case 'u': curtok.type=format_tokent::UNSIGNED_DEC; break;
    case 'x':
    case 'X': curtok.type=format_tokent::UNSIGNED_HEX; break;
    case 'e':
    case 'E': curtok.type=format_tokent::DOUBLE_ENG; break;
    case 'f':
    case 'F': curtok.type=format_tokent::DOUBLE; break;
    case 'g':
    case 'G': curtok.type=format_tokent::DOUBLE_G; break;
    case 'a':
    case 'A': curtok.type=format_tokent::DOUBLE_HEX; break;
    case 'c': curtok.type=format_tokent::CHAR; break;
    case 's': curtok.type=format_tokent::STRING; break;
    case 'p': curtok.type=format_tokent::POINTER; break;
    case '%': curtok.type=format_tokent::PERCENT; break;
    case '[': // pattern matching in, e.g., fscanf.
    {
      std::string tmp;
      it++;
      if(*it=='^') // if it's there, it must be first
      {
        tmp+='^'; it++;
        if(*it==']') // if it's there, it must be here
        {
          tmp+=']'; it++;
        }
      }

      for(;it!=arg_string.end() && *it!=']'; it++)
        tmp+=*it;

      break;
    }

    default: throw std::string("unsupported format conversion specifier: `") +
                               *it + "'";
  }
  it++;
}

/*******************************************************************\

Function: parse_format_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool parse_format_string(
  const exprt &format_arg,
  format_token_listt &token_list)
{
  token_list.clear();

  if(format_arg.id()==ID_string_constant)
  {
    const std::string &arg_string = id2string(format_arg.get(ID_value));

    std::string::const_iterator it=arg_string.begin();

    while(it!=arg_string.end())
    {
      if(*it=='%')
      {
        token_list.push_back(format_tokent());
        format_tokent &curtok=token_list.back();
        it++;

        parse_flags(it, curtok);
        parse_field_width(it, curtok);
        parse_precision(it, curtok);
        parse_length_modifier(it, curtok);
        parse_conversion_specifier(arg_string, it, curtok);
      }
      else
      {
        if(token_list.back().type!=format_tokent::TEXT)
          token_list.push_back(format_tokent(format_tokent::TEXT));

        std::string tmp;
        for(;it!=arg_string.end() && *it!='%';it++)
          tmp+=*it;

        token_list.back().value=tmp;
      }
    }

    return true;
  }

  return false; // non-const format string
}
