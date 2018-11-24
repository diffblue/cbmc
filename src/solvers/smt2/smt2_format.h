/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SMT2_SMT2_FORMAT_H
#define CPROVER_SOLVERS_SMT2_SMT2_FORMAT_H

#include <util/type.h>

struct smt2_format
{
  explicit smt2_format(const typet &_type) : type(_type)
  {
  }

  const typet &type;
};

std::ostream &operator<<(std::ostream &, const smt2_format &);

#endif // CPROVER_SOLVERS_SMT2_SMT2_FORMAT_H
