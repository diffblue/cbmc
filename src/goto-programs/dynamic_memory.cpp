/*******************************************************************\

Module: Abstraction for malloc

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cprover_prefix.h>
#include <std_expr.h>
#include <expr_util.h>

#include <ansi-c/c_types.h>

#include "dynamic_memory.h"

/*******************************************************************\

Function: deallocated

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt deallocated(const namespacet &ns, const exprt &pointer)
{
  // we check __CPROVER_deallocated!
  const symbolt &deallocated_symbol=ns.lookup(CPROVER_PREFIX "deallocated");

  exprt same_object_expr(ID_same_object, bool_typet());
  same_object_expr.copy_to_operands(pointer, symbol_expr(deallocated_symbol));
  
  return same_object_expr;
}

/*******************************************************************\

Function: dynamic_size

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt dynamic_size(const namespacet &ns, const exprt &pointer)
{
  // replace with CPROVER_alloc_size[POINTER_OBJECT(...)]

  exprt object_expr(ID_pointer_object, size_type());
  object_expr.copy_to_operands(pointer);

  exprt alloc_array=symbol_expr(ns.lookup(CPROVER_PREFIX "alloc_size"));

  #if 0
  std::cout << "AA: " << size_type().pretty() << std::endl;  
  std::cout << "AA: " << ns.follow(alloc_array.type()).pretty() << std::endl;  
  #endif

  assert(ns.follow(alloc_array.type()).subtype()==size_type());

  index_exprt result;
  result.array()=alloc_array;
  result.index()=object_expr;
  result.type()=size_type();
  
  return result;
}

/*******************************************************************\

Function: pointer_object_has_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt pointer_object_has_type(const exprt &pointer, const typet &type)
{
  return false_exprt();
}

/*******************************************************************\

Function: dynamic_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt dynamic_object(const exprt &pointer)
{
  exprt dynamic_expr(ID_dynamic_object, bool_typet());
  dynamic_expr.copy_to_operands(pointer);
  return dynamic_expr;
}

