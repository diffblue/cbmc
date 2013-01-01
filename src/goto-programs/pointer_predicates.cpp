/*******************************************************************\

Module: Various predicates over pointers in programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cprover_prefix.h>
#include <std_expr.h>
#include <expr_util.h>
#include <arith_tools.h>
#include <pointer_offset_size.h>

#include <ansi-c/c_types.h>

#include "pointer_predicates.h"

/*******************************************************************\

Function: same_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt same_object(const exprt &p1, const exprt &p2)
{
  return binary_relation_exprt(p1, ID_same_object, p2);
}

/*******************************************************************\

Function: object_size

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt object_size(const exprt &pointer)
{
  return unary_exprt(ID_object_size, pointer, index_type());
}

/*******************************************************************\

Function: pointer_offset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt pointer_offset(const exprt &pointer)
{
  return unary_exprt(ID_pointer_offset, pointer, index_type());
}

/*******************************************************************\

Function: deallocated

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt deallocated(const exprt &pointer, const namespacet &ns)
{
  // we check __CPROVER_deallocated!
  const symbolt &deallocated_symbol=ns.lookup(CPROVER_PREFIX "deallocated");

  return same_object(pointer, symbol_expr(deallocated_symbol));
}

/*******************************************************************\

Function: dynamic_size

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt dynamic_size(const namespacet &ns)
{
  return symbol_expr(ns.lookup(CPROVER_PREFIX "malloc_size"));
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

/*******************************************************************\

Function: good_pointer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt good_pointer(const exprt &pointer)
{
  return unary_exprt(ID_good_pointer, pointer, bool_typet());
}

/*******************************************************************\

Function: good_pointer_def

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt good_pointer_def(
  const exprt &pointer,
  const typet &dereference_type,
  const namespacet &ns)
{
  exprt bad_dynamic=
    or_exprt(deallocated(pointer, ns),
             dynamic_object_lower_bound(pointer),
             dynamic_object_upper_bound(pointer, dereference_type, ns));

  exprt good_dynamic=
    or_exprt(not_exprt(dynamic_object(pointer)), 
             not_exprt(bad_dynamic));

  exprt not_null=
    not_exprt(null_object(pointer));
  
  exprt not_invalid=
    not_exprt(invalid_pointer(pointer));
    
  exprt bad_other=
    or_exprt(object_lower_bound(pointer),
             object_upper_bound(pointer, dereference_type, ns));

  exprt good_other=
    or_exprt(dynamic_object(pointer),
             not_exprt(bad_other));

  return and_exprt(not_null, not_invalid, good_dynamic, good_other);
}

/*******************************************************************\

Function: null_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt null_object(const exprt &pointer)
{
  null_pointer_exprt null_pointer(to_pointer_type(pointer.type()));
  return same_object(null_pointer, pointer);
}

/*******************************************************************\

Function: null_pointer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt null_pointer(const exprt &pointer)
{
  null_pointer_exprt null_pointer(to_pointer_type(pointer.type()));
  return equal_exprt(pointer, null_pointer);
}

/*******************************************************************\

Function: invalid_pointer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt invalid_pointer(const exprt &pointer)
{
  return unary_exprt(ID_invalid_pointer, pointer, bool_typet());
}

/*******************************************************************\

Function: dynamic_object_lower_bound

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt dynamic_object_lower_bound(const exprt &pointer)
{
  return object_lower_bound(pointer);
}

/*******************************************************************\

Function: dynamic_object_upper_bound

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt dynamic_object_upper_bound(
  const exprt &pointer,
  const typet &dereference_type,
  const namespacet &ns)
{
  // this is
  // POINTER_OFFSET(p)+size>__CPROVER_malloc_size
  
  exprt malloc_size=dynamic_size(ns);

  exprt object_offset=pointer_offset(pointer);

  mp_integer element_size=
    pointer_offset_size(ns, dereference_type);

  if(element_size<0) element_size=0;

  exprt size=from_integer(element_size, object_offset.type());

  // need to add size
  exprt sum=plus_exprt(object_offset, size);

  if(ns.follow(sum.type())!=
     ns.follow(malloc_size.type()))
    sum.make_typecast(malloc_size.type());

  return binary_relation_exprt(sum, ID_gt, malloc_size);
}

/*******************************************************************\

Function: object_upper_bound

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt object_upper_bound(
  const exprt &pointer,
  const typet &dereference_type,
  const namespacet &ns)
{
  // this is
  // POINTER_OFFSET(p)+size>OBJECT_SIZE(pointer)
  
  exprt object_size_expr=object_size(pointer);

  exprt object_offset=pointer_offset(pointer);

  mp_integer element_size=
    pointer_offset_size(ns, dereference_type);

  if(element_size<0) element_size=0;

  exprt size=from_integer(element_size, object_offset.type());

  // need to add size
  exprt sum=plus_exprt(object_offset, size);

  if(ns.follow(sum.type())!=
     ns.follow(object_size_expr.type()))
    sum.make_typecast(object_size_expr.type());

  return binary_relation_exprt(sum, ID_gt, object_size_expr);
}

/*******************************************************************\

Function: object_lower_bound

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt object_lower_bound(const exprt &pointer)
{
  exprt zero=gen_zero(index_type());
  assert(zero.is_not_nil());

  return binary_relation_exprt(
    pointer_offset(pointer), ID_lt, zero);
}
