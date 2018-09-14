/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2irep.h"

#include <stack>

#include "smt2_tokenizer.h"

class smt2irept:public smt2_tokenizert
{
public:
  explicit smt2irept(std::istream &_in):smt2_tokenizert(_in)
  {
  }

  inline irept operator()()
  {
    parse();
    return result;
  }

  bool parse() override;

protected:
  irept result;
};

bool smt2irept::parse()
{
  std::stack<irept> stack;
  result.clear();

  while(true)
  {
    switch(next_token())
    {
    case END_OF_FILE:
      error() << "unexpected end of file" << eom;
      return true;

    case STRING_LITERAL:
    case NUMERAL:
    case SYMBOL:
      if(stack.empty())
      {
        result=irept(buffer);
        return false; // all done!
      }
      else
        stack.top().get_sub().push_back(irept(buffer));
      break;

    case OPEN: // '('
      // produce sub-irep
      stack.push(irept());
      break;

    case CLOSE: // ')'
      // done with sub-irep
      if(stack.empty())
      {
        error() << "unexpected ')'" << eom;
        return true;
      }
      else
      {
        irept tmp=stack.top();
        stack.pop();

        if(stack.empty())
        {
          result=tmp;
          return false; // all done!
        }

        stack.top().get_sub().push_back(tmp);
        break;
      }

    default:
      return true;
    }
  }
}

irept smt2irep(std::istream &in)
{
  return smt2irept(in)();
}
