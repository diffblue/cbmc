/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_C_SIZEOF_H
#define CPROVER_ANSI_C_C_SIZEOF_H

#include <util/namespace.h>
#include <util/expr.h>

class c_sizeoft
{
public:
  explicit c_sizeoft(const namespacet &_ns):ns(_ns)
  {
  }

  virtual ~c_sizeoft()
  {
  }

  exprt operator()(const typet &type)
  {
    return sizeof_rec(type);
  }

  exprt c_offsetof(
    const struct_typet &type,
    const irep_idt &component_name);

protected:
  const namespacet &ns;

  virtual exprt sizeof_rec(const typet &type);
};

exprt c_sizeof(
  const typet &src,
  const namespacet &ns);

exprt c_offsetof(
  const struct_typet &src,
  const irep_idt &component_name,
  const namespacet &ns);

#endif // CPROVER_ANSI_C_C_SIZEOF_H
