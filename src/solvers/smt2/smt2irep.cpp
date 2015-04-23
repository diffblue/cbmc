/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <stack>

#include "smt2irep.h"
#include "smt2_parser.h"

class smt2irept:public smt2_parsert
{
public:
  smt2irept(std::istream &_in):smt2_parsert(_in)
  {
  }
  
  inline irept operator()()
  {
    smt2_parsert::operator()();
    return result;
  }
  
protected:
  irept result;
  std::stack<irept> stack;

  // overload from smt2_parsert

  virtual void symbol()
  {
    if(stack.empty())
      result=irept(buffer);
    else
      stack.top().get_sub().push_back(irept(buffer));
  }
  
  virtual void string_literal()
  {
    symbol(); // we don't distinguish
  }
  
  virtual void numeral()
  {
    symbol(); // we don't distinguish
  }
  
  virtual void open_expression() // '('
  {
    // produce sub-irep
    stack.push(irept());
  }
  
  virtual void close_expression() // ')'
  {
    // done with sub-irep
    assert(!stack.empty()); // unexpected )

    irept tmp=stack.top();
    stack.pop();

    if(stack.empty())
      result=tmp;
    else
      stack.top().get_sub().push_back(tmp);
  }
  
  virtual void keyword()
  {
    // ignore
  }
  
  virtual void error(const std::string &message)
  {
  }
};

irept smt2irep(std::istream &in)
{
  return smt2irept(in)();
}
