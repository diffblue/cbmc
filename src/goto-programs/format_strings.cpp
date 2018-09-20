/*******************************************************************\

Module: Format String Parser

Author: CM Wintersteiger

\*******************************************************************/

/// \file
/// Format String Parser

#include "format_strings.h"

#include <util/exception_utils.h>
#include <util/std_types.h>
#include <util/std_expr.h>

#include <util/c_types.h>

#include <cctype>

void parse_flags(
  std::string::const_iterator &it,
  format_tokent &curtok)
{
  while(*it=='#' || *it=='0' ||
        *it=='-' || *it==' ' || *it=='+')
  {
    switch(*it)
    {
      case '#':
        curtok.flags.push_back(format_tokent::flag_typet::ALTERNATE); break;
      case '0':
        curtok.flags.push_back(format_tokent::flag_typet::ZERO_PAD); break;
      case '-':
        curtok.flags.push_back(format_tokent::flag_typet::LEFT_ADJUST); break;
      case ' ':
        curtok.flags.push_back(format_tokent::flag_typet::SIGNED_SPACE); break;
      case '+':
        curtok.flags.push_back(format_tokent::flag_typet::SIGN); break;
      default:
        throw unsupported_operation_exceptiont(
          std::string("unsupported format specifier flag: `") + *it + "'");
    }
    it++;
  }
}

void parse_field_width(
  std::string::const_iterator &it,
  format_tokent &curtok)
{
  if(*it=='*')
  {
    curtok.flags.push_back(format_tokent::flag_typet::ASTERISK);
    it++;
  }

  std::string tmp;
  for( ; isdigit(*it); it++) tmp+=*it;
  curtok.field_width=string2integer(tmp);
}

void parse_precision(
  std::string::const_iterator &it,
  format_tokent &curtok)
{
  if(*it=='.')
  {
    it++;

    if(*it=='*')
    {
      curtok.flags.push_back(format_tokent::flag_typet::ASTERISK);
      it++;
    }
    else
    {
      std::string tmp;
      for( ; isdigit(*it); it++) tmp+=*it;
      curtok.precision=string2integer(tmp);
    }
  }
}

void parse_length_modifier(
  std::string::const_iterator &it,
  format_tokent &curtok)
{
  if(*it=='h')
  {
    it++;
    if(*it=='h')
      it++;
    curtok.length_modifier = format_tokent::length_modifierst::LEN_h;
  }
  else if(*it=='l')
  {
    it++;
    if(*it=='l')
      it++;
    curtok.length_modifier = format_tokent::length_modifierst::LEN_l;
  }
  else if(*it=='L')
  {
    it++;
    curtok.length_modifier = format_tokent::length_modifierst::LEN_L;
  }
  else if(*it=='j')
  {
    it++;
    curtok.length_modifier = format_tokent::length_modifierst::LEN_j;
  }
  else if(*it=='t')
  {
    it++;
    curtok.length_modifier = format_tokent::length_modifierst::LEN_L;
  }
}

void parse_conversion_specifier(
  const std::string &arg_string,
  std::string::const_iterator &it,
  format_tokent &curtok)
{
  switch(*it)
  {
    case 'd':
    case 'i':
      curtok.type=format_tokent::token_typet::INT;
      curtok.representation=format_tokent::representationt::SIGNED_DEC;
      break;
    case 'o':
      curtok.type=format_tokent::token_typet::INT;
      curtok.representation=format_tokent::representationt::UNSIGNED_OCT;
      break;
    case 'u':
      curtok.type=format_tokent::token_typet::INT;
      curtok.representation=format_tokent::representationt::UNSIGNED_DEC;
      break;
    case 'x':
    case 'X':
      curtok.type=format_tokent::token_typet::INT;
      curtok.representation=format_tokent::representationt::UNSIGNED_HEX;
      break;
    case 'e':
    case 'E': curtok.type=format_tokent::token_typet::FLOAT; break;
    case 'f':
    case 'F': curtok.type=format_tokent::token_typet::FLOAT; break;
    case 'g':
    case 'G': curtok.type=format_tokent::token_typet::FLOAT; break;
    case 'a':
    case 'A': curtok.type=format_tokent::token_typet::FLOAT; break;
    case 'c': curtok.type=format_tokent::token_typet::CHAR; break;
    case 's': curtok.type=format_tokent::token_typet::STRING; break;
    case 'p': curtok.type=format_tokent::token_typet::POINTER; break;
    case '%':
      curtok.type=format_tokent::token_typet::TEXT;
      curtok.value="%";
      break;
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

      for( ; it!=arg_string.end() && *it!=']'; it++)
        tmp+=*it;

      break;
    }

    default:
      throw unsupported_operation_exceptiont(
        std::string("unsupported format conversion specifier: `") + *it + "'");
  }
  it++;
}

format_token_listt parse_format_string(const std::string &arg_string)
{
  format_token_listt token_list;

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
      if(token_list.empty() ||
         token_list.back().type!=format_tokent::token_typet::TEXT)
        token_list.push_back(format_tokent(format_tokent::token_typet::TEXT));

      std::string tmp;
      for( ; it!=arg_string.end() && *it!='%'; it++)
        tmp+=*it;

      INVARIANT(
        !token_list.empty() &&
        token_list.back().type == format_tokent::token_typet::TEXT,
        "must already have a TEXT token at the back of the token list");

      token_list.back().value=tmp;
    }
  }

  return token_list;
}

typet get_type(const format_tokent &token)
{
  switch(token.type)
  {
  case format_tokent::token_typet::INT:
    switch(token.length_modifier)
    {
    case format_tokent::length_modifierst::LEN_h:
      if(token.representation==format_tokent::representationt::SIGNED_DEC)
        return signed_char_type();
      else
        return unsigned_char_type();

    case format_tokent::length_modifierst::LEN_hh:
      if(token.representation==format_tokent::representationt::SIGNED_DEC)
        return signed_short_int_type();
      else
        return unsigned_short_int_type();

    case format_tokent::length_modifierst::LEN_l:
      if(token.representation==format_tokent::representationt::SIGNED_DEC)
        return signed_long_int_type();
      else
        return unsigned_long_int_type();

    case format_tokent::length_modifierst::LEN_ll:
      if(token.representation==format_tokent::representationt::SIGNED_DEC)
        return signed_long_long_int_type();
      else
        return unsigned_long_long_int_type();

    default:
      if(token.representation==format_tokent::representationt::SIGNED_DEC)
        return signed_int_type();
      else
        return unsigned_int_type();
    }

  case format_tokent::token_typet::FLOAT:
    switch(token.length_modifier)
    {
    case format_tokent::length_modifierst::LEN_l: return double_type();
    case format_tokent::length_modifierst::LEN_L: return long_double_type();
    default: return float_type();
    }

  case format_tokent::token_typet::CHAR:
    switch(token.length_modifier)
    {
    case format_tokent::length_modifierst::LEN_l: return wchar_t_type();
    default: return char_type();
    }

  case format_tokent::token_typet::POINTER:
    return pointer_type(void_type());

  case format_tokent::token_typet::STRING:
    switch(token.length_modifier)
    {
    case format_tokent::length_modifierst::LEN_l:
      return array_typet(wchar_t_type(), nil_exprt());
    default: return array_typet(char_type(), nil_exprt());
    }

  default:
    return nil_typet();
  }
}
