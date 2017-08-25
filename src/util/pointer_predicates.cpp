/*******************************************************************\

Module: Various predicates over pointers in programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Various predicates over pointers in programs

#include "pointer_predicates.h"

#include "c_types.h"
#include "cprover_prefix.h"
#include "namespace.h"
#include "std_expr.h"
#include "expr_util.h"
#include "arith_tools.h"
#include "pointer_offset_size.h"
#include "config.h"
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

exprt pointer_object_has_type(const exprt &pointer, const typet &type)
{
  return false_exprt();
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
  const pointer_typet &pointer_type=to_pointer_type(ns.follow(pointer.type()));
  const typet &dereference_type=pointer_type.subtype();

  exprt good_dynamic_tmp1=
    or_exprt(
      not_exprt(malloc_object(pointer, ns)),
      and_exprt(
        not_exprt(
          dynamic_object_lower_bound(
            pointer,
            ns,
            nil_exprt())),
        not_exprt(
          dynamic_object_upper_bound(
            pointer,
            dereference_type,
            ns,
            size_of_expr(dereference_type, ns)))));

  exprt good_dynamic_tmp2=
    and_exprt(not_exprt(deallocated(pointer, ns)),
              good_dynamic_tmp1);

  exprt good_dynamic=
    or_exprt(not_exprt(dynamic_object(pointer)),
             good_dynamic_tmp2);

  exprt not_null=
    not_exprt(null_pointer(pointer));

  exprt not_invalid=
    not_exprt(invalid_pointer(pointer));

  exprt bad_other=
    or_exprt(object_lower_bound(pointer, ns, nil_exprt()),
             object_upper_bound(
               pointer,
               dereference_type,
               ns,
               size_of_expr(dereference_type, ns)));

  exprt good_other=
    or_exprt(dynamic_object(pointer),
             not_exprt(bad_other));

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
  const namespacet &ns,
  const exprt &offset)
{
  return object_lower_bound(pointer, ns, offset);
}

exprt dynamic_object_upper_bound(
  const exprt &pointer,
  const typet &dereference_type,
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

    if(ns.follow(object_offset.type())!=
       ns.follow(access_size.type()))
      object_offset.make_typecast(access_size.type());
    sum=plus_exprt(object_offset, access_size);
  }

  if(ns.follow(sum.type())!=
     ns.follow(malloc_size.type()))
    sum.make_typecast(malloc_size.type());

  return binary_relation_exprt(sum, op, malloc_size);
}

exprt object_upper_bound(
  const exprt &pointer,
  const typet &dereference_type,
  const namespacet &ns,
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

    if(ns.follow(object_offset.type())!=
       ns.follow(access_size.type()))
      object_offset.make_typecast(access_size.type());
    sum=plus_exprt(object_offset, access_size);
  }


  if(ns.follow(sum.type())!=
     ns.follow(object_size_expr.type()))
    sum.make_typecast(object_size_expr.type());

  return binary_relation_exprt(sum, op, object_size_expr);
}

exprt object_lower_bound(
  const exprt &pointer,
  const namespacet &ns,
  const exprt &offset)
{
  exprt p_offset=pointer_offset(pointer);

  exprt zero=from_integer(0, p_offset.type());
  assert(zero.is_not_nil());

  if(offset.is_not_nil())
  {
    if(ns.follow(p_offset.type())!=ns.follow(offset.type()))
      p_offset=
        plus_exprt(p_offset, typecast_exprt(offset, p_offset.type()));
    else
      p_offset=plus_exprt(p_offset, offset);
  }

  return binary_relation_exprt(p_offset, ID_lt, zero);
}
