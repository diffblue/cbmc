/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_FORMATTER_H
#define CPROVER_ANSI_C_FORMATTER_H

#include <util/formatter.h>

class ansi_c_formattert : public formattert
{
public:
  explicit ansi_c_formattert(const namespacet &_ns) : ns(_ns)
  {
  }

  std::ostream &format(std::ostream &, const exprt &) override;
  std::ostream &format(std::ostream &, const typet &) override;
  std::ostream &format(std::ostream &, const source_locationt &) override;

  const namespacet &ns;
};

#endif // CPROVER_ANSI_C_FORMATTER_H
