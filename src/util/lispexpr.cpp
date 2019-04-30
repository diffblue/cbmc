/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "lispexpr.h"

#include "string_utils.h"

#include <iostream>

std::string lispexprt::expr2string() const
{
  std::string result;

  switch(type)
  {
    case Number:
    case Symbol:
      result=value;
      break;

    case List:
      result="(";
      for(std::size_t j=0; j<size(); j++)
      {
        if((j+1)==size() && size()!=1)
        {
          if((*this)[j].is_nil())
            break;
          result+=" . ";
        }
        else if(j!=0)
          result+=' ';

        result+=(*this)[j].expr2string();
      }
      result+=')';
      break;

    case String:
      result="\"";
      result+=escape(value);
      result+="\"";
      break;
  }

  return result;
}

bool lispexprt::parse(const std::string &s)
{
  std::string::size_type ptr=0;
  return parse(s, ptr);
}

bool lispexprt::parse(
  const std::string &s,
  std::string::size_type &ptr)
{
  clear();
  value.clear();

  if(ptr==std::string::npos || ptr>=s.size())
    return true;

  // we ignore whitespace
  ptr=s.find_first_not_of(" \t", ptr);
  if(ptr==std::string::npos)
    return true;

  if(s[ptr]=='(') // LispCons
  {
    type=List;
    lispexprt expr;

    for(ptr++; ptr<s.size();)
    {
      bool dot=false;

      if(ptr<s.size() && s[ptr]=='.')
      {
        dot=true;
        ptr++;
      }

      if(expr.parse(s, ptr))
        return true;
      push_back(expr);

      if(ptr<s.size() && s[ptr]==')')
      {
        if(!dot && size()>1)
        {
          expr.parse("nil");
          push_back(expr);
        }

        ptr++;
        break;
      }
    }
  }
  else if(s[ptr]=='"') // LispString
  {
    type=String;
    bool quoted=false;

    value.reserve(50); // guessing - will be adjusted automatically

    for(ptr++; ptr<s.size() && (s[ptr]!='"' && !quoted); ptr++)
    {
      if(!quoted && s[ptr]=='\\')
        quoted=true;
      else
      {
        quoted=false;
        value+=s[ptr];
      }
    }

    if(ptr<s.size())
      ptr++;
  }
  else if(isdigit(s[ptr])) // LispNumber
  {
    value.reserve(10); // guessing - will be adjusted automatically

    type=Number;
    for(; ptr<s.size() && (isdigit(s[ptr]) || s[ptr]=='.'); ptr++)
      value+=s[ptr];
  }
  else // must be LispSymbol
  {
    value.reserve(20); // guessing - will be adjusted automatically

    type=Symbol;
    for(; ptr<s.size() && s[ptr]!=' ' && s[ptr]!='\t' &&
        s[ptr]!=')' && s[ptr]!='.'; ptr++)
      value+=s[ptr];
  }

  // we ignore whitespace
  ptr=s.find_first_not_of(" \t", ptr);

  return false;
}

int test_lispexpr()
{
  std::string line;
  char ch;

  while(true)
  {
    line.clear();

    while(true)
    {
      if(!std::cin.read(&ch, 1))
        return 0;

      if(ch=='\n')
      {
        lispexprt expr;
        if(expr.parse(line))
          std::cout << "Parsing error\n";
        else
          std::cout << expr << "\n";

        break;
      }

      line+=ch;
    }
  }

  return 0;
}
