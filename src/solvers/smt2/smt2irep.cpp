/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2irep.h"

#include <util/message.h>

#include <stack>

#include "smt2_tokenizer.h"

class smt2irept
{
public:
  explicit smt2irept(smt2_tokenizert &_tokenizer)
    : tokenizer(_tokenizer)
  {
  }

  std::optional<irept> operator()();

protected:
  smt2_tokenizert tokenizer;
};

std::optional<irept> smt2irept::operator()()
{
  std::stack<irept> stack;

  while(true)
  {
    switch(tokenizer.next_token())
    {
    case smt2_tokenizert::END_OF_FILE:
      if(stack.empty())
        return {};
      else
        throw tokenizer.error("unexpected end of file");

    case smt2_tokenizert::STRING_LITERAL:
    case smt2_tokenizert::NUMERAL:
    case smt2_tokenizert::SYMBOL:
      if(stack.empty())
        return irept(tokenizer.get_buffer()); // all done!
      else
        stack.top().get_sub().push_back(irept(tokenizer.get_buffer()));
      break;

    case smt2_tokenizert::OPEN: // '('
      // produce sub-irep
      stack.push(irept());
      break;

    case smt2_tokenizert::CLOSE: // ')'
      // done with sub-irep
      if(stack.empty())
        throw tokenizer.error("unexpected ')'");
      else
      {
        irept tmp = stack.top();
        stack.pop();

        if(stack.empty())
          return tmp; // all done!

        stack.top().get_sub().push_back(tmp);
        break;
      }

    case smt2_tokenizert::NONE:
    case smt2_tokenizert::KEYWORD:
      throw tokenizer.error("unexpected token");
    }
  }
}

std::optional<irept>
smt2irep(std::istream &in, message_handlert &message_handler)
{
  try
  {
    smt2_tokenizert tokenizer{in};
    return smt2irept{tokenizer}();
  }
  catch(const smt2_tokenizert::smt2_errort &e)
  {
    messaget log{message_handler};
    log.error().source_location.set_line(e.get_line_no());
    log.error() << e.what() << messaget::eom;
    return {};
  }
}

std::optional<irept>
smt2irep(smt2_tokenizert &tokenizer)
{
  return smt2irept{tokenizer}();
}
