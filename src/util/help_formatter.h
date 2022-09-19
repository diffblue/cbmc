/*******************************************************************\

Module: Help Formatter

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Help Formatter

#ifndef CPROVER_UTIL_HELP_FORMATTER_H
#define CPROVER_UTIL_HELP_FORMATTER_H

#include <iosfwd>
#include <string>

class help_formattert
{
public:
  explicit help_formattert(const std::string &_s) : s(_s)
  {
  }

  const std::string &s;
  void operator()(std::ostream &) const;

protected:
  struct statet
  {
    std::size_t column = 0;
    bool aligning = false;
    std::string word = "";
  };

  static void emit_word(statet &, std::ostream &);
  static const std::size_t first_column_width = 29;
};

static inline help_formattert help_formatter(const std::string &s)
{
  return help_formattert(s);
}

static inline std::ostream &
operator<<(std::ostream &out, const help_formattert &h)
{
  h(out);
  return out;
}

#endif // CPROVER_UTIL_HELP_FORMATTER_H
