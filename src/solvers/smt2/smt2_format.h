/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SMT2_SMT2_FORMAT_H
#define CPROVER_SOLVERS_SMT2_SMT2_FORMAT_H

#include <util/expr.h>

template <typename T>
struct smt2_format_containert
{
  explicit smt2_format_containert(const T &_o) : o(_o)
  {
  }

  const T &o;
};

template <typename T>
static inline smt2_format_containert<T> smt2_format(const T &_o)
{
  return smt2_format_containert<T>(_o);
}

template <typename T>
static inline std::ostream &
operator<<(std::ostream &out, const smt2_format_containert<T> &c)
{
  return smt2_format_rec(out, c.o);
}

std::ostream &smt2_format_rec(std::ostream &, const exprt &);
std::ostream &smt2_format_rec(std::ostream &, const typet &);

#endif // CPROVER_SOLVERS_SMT2_SMT2_FORMAT_H
