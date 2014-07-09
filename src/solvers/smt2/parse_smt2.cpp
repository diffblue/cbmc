/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stack>

#include "parse_smt2.h"

/*******************************************************************\

Function: parse_smt2

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irept parse_smt2(const std::string &src)
{
  std::size_t pos=0;
  irept result;
  std::stack<irept *> stack;
  
  stack.push(&result);
  
  while(!stack.empty())
  {
    // skip any spaces
    while(pos<src.size() && src[pos]==' ') pos++;

    if(pos>=src.size())
    {
      // blank
      stack.pop();
    }
    else if(src[pos]=='(')
    {
      // produce sub-irep
      stack.top()->get_sub().push_back(irept());
      stack.push(&stack.top()->get_sub().front());
      pos++;
    }
    else if(src[pos]==')')
    {
      // done with sub-irep
      stack.pop();
      pos++;
    }
    else if(src[pos]=='|')
    {
      // get token
      std::size_t start=pos;
      while(pos<src.size() && src[pos]!='|') pos++;
      std::string token=src.substr(start, pos-start);
      stack.top()->get_sub().push_back(irept(token));
    }
    else
    {
      // get token
      std::size_t start=pos;
      while(pos<src.size() && src[pos]!=' ' && src[pos]!='(' && src[pos]!=')') pos++;
      std::string token=src.substr(start, pos-start);
      stack.top()->get_sub().push_back(irept(token));
    }
  }
  
  return result;
}
