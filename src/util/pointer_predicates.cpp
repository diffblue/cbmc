/*******************************************************************\

Module: Various predicates over pointers in programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Various predicates over pointers in programs

#include "pointer_predicates.h"

#include "arith_tools.h"
#include "c_types.h"
#include "cprover_prefix.h"
#include "namespace.h"
#include "pointer_offset_size.h"
#include "std_expr.h"
#include "symbol.h"

exprt pointer_object(const exprt &p)
{
  return unary_exprt(ID_pointer_object, p, size_type());
}

exprt same_object(const exprt &p1, const exprt &p2)
{
  return equal_exprt(pointer_object(p1), pointer_object(p2));
}

exprt object_size(const exprt &pointer)
{
  return unary_exprt(ID_object_size, pointer, size_type());
}

exprt pointer_offset(const exprt &pointer)
{
  return unary_exprt(ID_pointer_offset, pointer, signed_size_type());
}

exprt malloc_object(const exprt &pointer, const namespacet &ns)
{
  // we check __CPROVER_malloc_object!
  const symbolt &malloc_object_symbol=ns.lookup(CPROVER_PREFIX "malloc_object");

  return same_object(pointer, malloc_object_symbol.symbol_expr());
}

exprt deallocated(const exprt &pointer, const namespacet &ns)
{
  // we check __CPROVER_deallocated!
  const symbolt &deallocated_symbol=ns.lookup(CPROVER_PREFIX "deallocated");

  return same_object(pointer, deallocated_symbol.symbol_expr());
}

exprt dead_object(const exprt &pointer, const namespacet &ns)
{
  // we check __CPROVER_dead_object!
  const symbolt &deallocated_symbol=ns.lookup(CPROVER_PREFIX "dead_object");

  return same_object(pointer, deallocated_symbol.symbol_expr());
}

exprt dynamic_size(const namespacet &ns)
{
  return ns.lookup(CPROVER_PREFIX "malloc_size").symbol_expr();
}

exprt dynamic_object(const exprt &pointer)
{
  exprt dynamic_expr(ID_dynamic_object, bool_typet());
  dynamic_expr.copy_to_operands(pointer);
  return dynamic_expr;
}

exprt good_pointer(const exprt &pointer)
{
  return unary_exprt(ID_good_pointer, pointer, bool_typet());
}

exprt good_pointer_def(
  const exprt &pointer,
  const namespacet &ns)
{
  const pointer_typet &pointer_type = to_pointer_type(pointer.type());
  const typet &dereference_type=pointer_type.subtype();

  const or_exprt good_dynamic_tmp1(
    not_exprt(malloc_object(pointer, ns)),
    and_exprt(
      not_exprt(dynamic_object_lower_bound(pointer, nil_exprt())),
      not_exprt(dynamic_object_upper_bound(
        pointer, ns, size_of_expr(dereference_type, ns)))));

  const and_exprt good_dynamic_tmp2(
    not_exprt(deallocated(pointer, ns)), good_dynamic_tmp1);

  const or_exprt good_dynamic(
    not_exprt(dynamic_object(pointer)), good_dynamic_tmp2);

  const not_exprt not_null(null_pointer(pointer));

  const not_exprt not_invalid(invalid_pointer(pointer));

  const or_exprt bad_other(
    object_lower_bound(pointer, nil_exprt()),
    object_upper_bound(pointer, size_of_expr(dereference_type, ns)));

  const or_exprt good_other(dynamic_object(pointer), not_exprt(bad_other));

  return and_exprt(
    not_null,
    not_invalid,
    good_dynamic,
    good_other);
}

exprt null_object(const exprt &pointer)
{
  null_pointer_exprt null_pointer(to_pointer_type(pointer.type()));
  return same_object(null_pointer, pointer);
}

exprt integer_address(const exprt &pointer)
{
  null_pointer_exprt null_pointer(to_pointer_type(pointer.type()));
  return and_exprt(same_object(null_pointer, pointer),
                   notequal_exprt(null_pointer, pointer));
}

exprt null_pointer(const exprt &pointer)
{
  null_pointer_exprt null_pointer(to_pointer_type(pointer.type()));
  return same_object(pointer, null_pointer);
}

exprt invalid_pointer(const exprt &pointer)
{
  return unary_exprt(ID_invalid_pointer, pointer, bool_typet());
}

exprt dynamic_object_lower_bound(
  const exprt &pointer,
  const exprt &offset)
{
  return object_lower_bound(pointer, offset);
}

exprt dynamic_object_upper_bound(
  const exprt &pointer,
  const namespacet &ns,
  const exprt &access_size)
{
  // this is
  // POINTER_OFFSET(p)+access_size>__CPROVER_malloc_size

  exprt malloc_size=dynamic_size(ns);

  exprt object_offset=pointer_offset(pointer);

  // need to add size
  irep_idt op=ID_ge;
  exprt sum=object_offset;

  if(access_size.is_not_nil())
  {
    op=ID_gt;

    sum = plus_exprt(
      typecast_exprt::conditional_cast(object_offset, access_size.type()),
      access_size);
  }

  return binary_relation_exprt(
    typecast_exprt::conditional_cast(sum, malloc_size.type()), op, malloc_size);
}

exprt object_upper_bound(
  const exprt &pointer,
  const exprt &access_size)
{
  // this is
  // POINTER_OFFSET(p)+access_size>OBJECT_SIZE(pointer)

  exprt object_size_expr=object_size(pointer);

  exprt object_offset=pointer_offset(pointer);

  // need to add size
  irep_idt op=ID_ge;
  exprt sum=object_offset;

  if(access_size.is_not_nil())
  {
    op=ID_gt;

    sum = plus_exprt(
      typecast_exprt::conditional_cast(object_offset, access_size.type()),
      access_size);
  }

  return binary_relation_exprt(
    typecast_exprt::conditional_cast(sum, object_size_expr.type()),
    op,
    object_size_expr);
}

exprt object_lower_bound(
  const exprt &pointer,
  const exprt &offset)
{
  exprt p_offset=pointer_offset(pointer);

  exprt zero=from_integer(0, p_offset.type());
  CHECK_RETURN(zero.is_not_nil());

  if(offset.is_not_nil())
  {
    p_offset = plus_exprt(
      p_offset, typecast_exprt::conditional_cast(offset, p_offset.type()));
  }

  return binary_relation_exprt(p_offset, ID_lt, zero);
}
