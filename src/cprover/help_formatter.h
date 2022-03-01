/*******************************************************************\

Module: Help Formatter

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Help Formatter

#ifndef CPROVER_CPROVER_HELP_FORMATTER_H
#define CPROVER_CPROVER_HELP_FORMATTER_H

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

#endif // CPROVER_CPROVER_HELP_FORMATTER_H
