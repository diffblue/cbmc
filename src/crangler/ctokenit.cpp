/*******************************************************************\

Module: C Token Iterator

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// ctokenit

#include "ctokenit.h"

#include <util/exception_utils.h>
#include <util/invariant.h>

#include <algorithm>

const ctokent &ctokenitt::operator*() const
{
  PRECONDITION(!eof());
  return tokens[pos];
}

ctokenitt ctokenitt::operator++(int) // NOLINT(*)
{
  PRECONDITION(!eof());
  auto pre_increment = *this; // copy
  pos++;
  return pre_increment;
}

ctokenitt match_bracket(ctokenitt t, char open, char close)
{
  if(!t)
    return t;

  // skip whitespace, if any
  while(t && (is_ws(*t) || is_comment(*t) || is_preprocessor_directive(*t)))
    t++;

  if(*t != open)
    return t;

  std::size_t bracket_count = 0;
  while(true)
  {
    if(!t)
      throw invalid_source_file_exceptiont("expected " + std::string(1, close));

    const auto &token = *(t++);

    if(token == open)
      bracket_count++;
    else if(token == close)
    {
      bracket_count--;
      if(bracket_count == 0)
        return t; // done
    }
  }
}

ctokenitt
match_bracket(ctokenitt t, char open, char close, ctokenitt::tokenst &dest)
{
  auto end = match_bracket(t, open, close);
  std::copy(t.cit(), end.cit(), dest.end());
  return end;
}
