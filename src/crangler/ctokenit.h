/*******************************************************************\

Module: C Token Iterator

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// ctokenit

#ifndef CPROVER_CRANGLER_CTOKENIT_H
#define CPROVER_CRANGLER_CTOKENIT_H

#include "cscanner.h"

class ctokenitt
{
public:
  using tokenst = std::vector<ctokent>;

  explicit ctokenitt(const tokenst &__tokens) : tokens(__tokens)
  {
  }

  explicit operator bool() const
  {
    return !eof();
  }

  bool eof() const
  {
    return pos >= tokens.size();
  }

  ctokenitt &operator+=(std::size_t offset)
  {
    pos += offset;
    return *this;
  }

  ctokenitt operator++(int); // postfix ++

  const ctokent &operator*() const;

  const ctokent *operator->() const
  {
    return &**this;
  }

  tokenst::const_iterator cit() const
  {
    return tokens.begin() + pos;
  }

  bool operator!=(const ctokenitt &other) const
  {
    return pos != other.pos;
  }

protected:
  const tokenst &tokens;
  std::size_t pos = 0;
};

ctokenitt match_bracket(ctokenitt, char open, char close);
ctokenitt
match_bracket(ctokenitt, char open, char close, ctokenitt::tokenst &dest);

#endif // CPROVER_CRANGLER_CTOKENIT_H
