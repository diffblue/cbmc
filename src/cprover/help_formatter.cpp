/*******************************************************************\

Module: Help Formatter

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "help_formatter.h"

#include "console.h"

#include <ostream>

void help_formattert::operator()(std::ostream &out) const
{
  std::size_t pos = 0;
  auto next = [this, &pos]() -> char {
    if(pos < s.size())
      return s[pos++];
    else
      return 0;
  };

  std::size_t col = 0;

  while(pos < s.size())
  {
    auto ch = next();

    if(ch == '{')
    {
      auto what = next();
      switch(what)
      {
      case 'b':
        out << consolet::bold;
        break;
      case 'u':
        out << consolet::underline;
        break;
      case 'y':
        out << consolet::yellow;
        break;
      default:
        break;
      }

      while(pos < s.size() && (ch = next()) != '}')
      {
        out << ch;
        col++;
      }

      out << consolet::reset;
    }
    else if(ch == '\t')
    {
      if(col < 29)
      {
        out << std::string(29 - col, ' ');
        col = 40;
      }
    }
    else if(ch == '\n')
    {
      out << ch;
      col = 0;
    }
    else
    {
      out << ch;
      col++;
    }
  }
}
