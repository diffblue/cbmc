/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CPP_FORMATTER_H
#define CPROVER_CPP_FORMATTER_H

#include <util/formatter.h>

class cpp_formattert : public formattert
{
public:
  explicit cpp_formattert(const namespacet &_ns) : ns(_ns)
  {
  }

  std::ostream &format(std::ostream &, const exprt &) override;
  std::ostream &format(std::ostream &, const typet &) override;
  std::ostream &format(std::ostream &, const source_locationt &) override;

  const namespacet &ns;
};

#endif // CPROVER_CPP_FORMATTER_H
