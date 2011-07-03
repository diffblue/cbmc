/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <namespace.h>

#include "expr.h"

class c_sizeoft
{
public:
  c_sizeoft(const namespacet &_ns):ns(_ns)
  {
  }
  
  virtual ~c_sizeoft()
  {
  }

  exprt operator()(const typet &type)
  {
    return c_sizeof(type);
  }

  exprt c_offsetof(
    const struct_typet &type,
    const irep_idt &component_name);

protected:
  const namespacet &ns;

  virtual exprt sizeof_rec(const typet &type);
  
  exprt c_sizeof(const typet &type)
  {
    exprt result(sizeof_rec(type));
    
    if(result.is_nil()) return result;
    
    result.set(ID_C_c_sizeof_type, type);
    return result;
  }
};

exprt c_sizeof(const typet &src, const namespacet &ns);

exprt c_offsetof(
  const struct_typet &src,
  const irep_idt &component_name,
  const namespacet &ns);
