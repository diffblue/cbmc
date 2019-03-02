/*******************************************************************\

Module: Local variables whose address is taken

Author: Daniel Kroening

Date: March 2013

\*******************************************************************/

/// \file
/// Local variables whose address is taken

#ifndef CPROVER_ANALYSES_LOCALS_H
#define CPROVER_ANALYSES_LOCALS_H

#include <goto-programs/goto_function.h>

class localst
{
public:
  explicit localst(const goto_functiont &goto_function)
  {
    build(goto_function);
  }

  void output(std::ostream &out) const;

  // Returns true for all procedure-local variables,
  // not including those with static storage duration,
  // but including the function parameters.
  bool is_local(const irep_idt &identifier) const
  {
    return locals.find(identifier) != locals.end();
  }

  typedef std::unordered_set<irep_idt> locals_sett;
  locals_sett locals;

protected:
  void build(const goto_functiont &goto_function);
};

inline std::ostream &operator<<(
  std::ostream &out, const localst &locals)
{
  locals.output(out);
  return out;
}

#endif // CPROVER_ANALYSES_LOCALS_H
