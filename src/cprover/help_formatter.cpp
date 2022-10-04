/*******************************************************************\

Module: Help Formatter

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "help_formatter.h"

#include "console.h"

#include <ostream>

void help_formattert::emit_word(statet &state, std::ostream &out)
{
  if(state.word.empty())
    return;

  // screen width exceeded when aligning?
  if(state.column + state.word.size() > consolet::width() && state.aligning)
  {
    out << '\n' << std::string(first_column_width + 1, ' ');
    state.column = first_column_width + 1;
  }

  out << state.word;
  state.column += state.word.size();
  state.word.clear();
}

void help_formattert::operator()(std::ostream &out) const
{
  std::size_t pos = 0;
  auto next = [this, &pos]() -> char {
    if(pos < s.size())
      return s[pos++];
    else
      return 0;
  };

  statet state;

  while(pos < s.size())
  {
    auto ch = next();

    if(ch == '{')
    {
      emit_word(state, out);

      auto what = next();
      // spaces in formatted text are non-breakable
      while(pos < s.size() && (ch = next()) != '}')
        state.word += ch;

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

      emit_word(state, out);
      out << consolet::reset;
    }
    else if(ch == '\t')
    {
      emit_word(state, out);
      if(state.column < first_column_width)
      {
        out << std::string(first_column_width - state.column, ' ');
        state.column = first_column_width;
      }
      state.aligning = true;
    }
    else if(ch == '\n')
    {
      emit_word(state, out);
      out << '\n';
      state.column = 0;
      state.aligning = false;
    }
    else
    {
      state.word += ch;
      if(ch == ' ')
        emit_word(state, out);
    }
  }

  emit_word(state, out);
}
