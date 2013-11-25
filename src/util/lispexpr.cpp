/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include "lispexpr.h"

/*******************************************************************\

Function: lispexprt::expr2string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    for(unsigned j=0; j<size(); j++)
    {
      if((j+1)==size() && size()!=1)
      {
        if((*this)[j].is_nil()) break;
        result+=" . ";
      }
      else if(j!=0)
        result+=" ";

      result+=(*this)[j].expr2string();
    }
    result+=")";
    break;

   case String:
    result="\"";
    result+=escape(value);
    result+="\"";
    break;
  }

  return result;
}

/*******************************************************************\

Function: lispexprt::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool lispexprt::parse(const std::string &s)
{
  unsigned ptr=0;
  return parse(s, ptr);
}

/*******************************************************************\

Function: lispexprt::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool lispexprt::parse(const std::string &s, unsigned &ptr)
{
  clear();
  value="";

  if(ptr>=s.size()) return true;

  // we ignore whitespace
  for(; ptr<s.size() && (s[ptr]==' ' || s[ptr]=='\t'); ptr++);

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

      if(expr.parse(s, ptr)) return true;
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

    if(ptr<s.size()) ptr++;
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
  for(; ptr<s.size() && (s[ptr]==' ' || s[ptr]=='\t'); ptr++);

  return false;
}

/*******************************************************************\

Function: escape

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string escape(const std::string &s)
{
  std::string result;

  for(unsigned i=0; i<s.size(); i++)
  {
    if(s[i]=='\\' || s[i]=='"')
      result+='\\';

    result+=s[i];
  }

  return result;
}

/*******************************************************************\

Function: test_lispexpr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int test_lispexpr()
{
  std::string line;
  char ch;

  while(true)
  {
    line="";

    while(true)
    {
      if(!std::cin.read(&ch, 1)) return 0;

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

