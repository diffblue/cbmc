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
  std::stack<irept> stack;
  stack.push(irept());

  while(pos<src.size())
  {
    if(src[pos]==' ') // skip any spaces
    {
      pos++;
    }
    else if(src[pos]=='(')
    {
      // produce sub-irep
      stack.push(irept());
      pos++;
    }
    else if(src[pos]==')')
    {
      // done with sub-irep
      if(stack.size()<=1) return irept(); // too many )
      irept tmp=stack.top();
      stack.pop();
      stack.top().get_sub().push_back(tmp);
      pos++;
    }
    else if(src[pos]=='|')
    {
      // get token
      std::size_t start=pos;
      pos++;
      while(pos<src.size() && src[pos]!='|') pos++;
      if(pos<src.size()) pos++;
      std::string token=src.substr(start, pos-start);
      stack.top().get_sub().push_back(irept(token));
    }
    else
    {
      // get token
      std::size_t start=pos;
      while(pos<src.size() && src[pos]!=' ' && src[pos]!='(' && src[pos]!=')') pos++;
      std::string token=src.substr(start, pos-start);
      stack.top().get_sub().push_back(irept(token));
    }
  }

  // The stack should really have size 1, or it's a parse error

  if(stack.size()==1 && stack.top().get_sub().size()==1)
    return stack.top().get_sub().front();
  else
    return irept();
}
