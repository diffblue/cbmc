/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "dereference.h"

#ifdef DEBUG
#include <iostream>
#include <util/format_expr.h>
#endif

#include <util/std_expr.h>
#include <util/byte_operators.h>
#include <util/pointer_offset_size.h>
#include <util/base_type.h>
#include <util/simplify_expr.h>
#include <util/arith_tools.h>

#include <util/c_types.h>

exprt dereferencet::operator()(const exprt &pointer)
{
  if(pointer.type().id()!=ID_pointer)
    throw "dereference expected pointer type, but got "+
          pointer.type().pretty();

  // type of the object
  const typet &type=pointer.type().subtype();

  #ifdef DEBUG
  std::cout << "DEREF: " << format(pointer) << '\n';
  #endif

  return dereference_rec(
    pointer,
    from_integer(0, index_type()), // offset
    type);
}

/// \return Expression equivalent to `byte_extract(object, offset)` and of type
///   `type`. The expression is potentially simplified so that for instance in
///   the case of an array, `object[offset]` can be returned.
exprt dereferencet::read_object(
  const exprt &object,
  const exprt &offset,
  const typet &type)
{
  const typet &object_type=ns.follow(object.type());
  const typet &dest_type=ns.follow(type);

  // is the object an array with matching subtype?

  exprt simplified_offset=simplify_expr(offset, ns);

  // check if offset is zero
  if(simplified_offset.is_zero())
  {
    // check type
    if(base_type_eq(object_type, dest_type, ns))
    {
      return object; // trivial case
    }
    else if(type_compatible(object_type, dest_type))
    {
      // the type differs, but we can do this with a typecast
      return typecast_exprt(object, dest_type);
    }
  }

  if(object.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(object);

    exprt index=index_expr.index();

    // multiply index by object size
    exprt size=size_of_expr(object_type, ns);

    if(size.is_nil())
      throw "dereference failed to get object size for index";

    index.make_typecast(simplified_offset.type());
    size.make_typecast(index.type());

    const plus_exprt new_offset(simplified_offset, mult_exprt(index, size));

    return read_object(index_expr.array(), new_offset, type);
  }
  else if(object.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(object);

    const typet &compound_type=
      ns.follow(member_expr.struct_op().type());

    if(compound_type.id()==ID_struct)
    {
      const struct_typet &struct_type=
        to_struct_type(compound_type);

      exprt member_offset=member_offset_expr(
        struct_type, member_expr.get_component_name(), ns);

      if(member_offset.is_nil())
        throw "dereference failed to get member offset";

      member_offset.make_typecast(simplified_offset.type());

      const plus_exprt new_offset(simplified_offset, member_offset);

      return read_object(member_expr.struct_op(), new_offset, type);
    }
    else if(compound_type.id()==ID_union)
    {
      // Unions are easy: the offset is always zero,
      // so simply pass down.
      return read_object(member_expr.struct_op(), offset, type);
    }
  }

  // check if we have an array with the right subtype
  if(object_type.id()==ID_array &&
     base_type_eq(object_type.subtype(), dest_type, ns))
  {
    // check proper alignment
    exprt size=size_of_expr(dest_type, ns);

    if(size.is_not_nil())
    {
      mp_integer size_constant, offset_constant;
      if(!to_integer(simplify_expr(size, ns), size_constant) &&
         !to_integer(simplified_offset, offset_constant) &&
         (offset_constant%size_constant)==0)
      {
        // Yes! Can use index expression!
        mp_integer index_constant=offset_constant/size_constant;
        exprt index_expr=from_integer(index_constant, size.type());
        return index_exprt(object, index_expr, dest_type);
      }
    }
  }

  // give up and use byte_extract
  return byte_extract_exprt(
    byte_extract_id(), object, simplified_offset, dest_type);
}

/// Attempt to dereference the object at address `address + offset` and of
/// type `type`. Throws an exception if unsuccessful.
exprt dereferencet::dereference_rec(
  const exprt &address,
  const exprt &offset,
  const typet &type)
{
  if(address.id()==ID_address_of)
  {
    const address_of_exprt &address_of_expr=to_address_of_expr(address);

    const exprt &object=address_of_expr.object();

    return read_object(object, offset, type);
  }
  else if(address.id()==ID_typecast)
  {
    const typecast_exprt &typecast_expr=to_typecast_expr(address);

    return dereference_typecast(typecast_expr, offset, type);
  }
  else if(address.id()==ID_plus)
  {
    // pointer arithmetic
    if(address.operands().size()<2)
      throw "plus with less than two operands";

    return dereference_plus(address, offset, type);
  }
  else if(address.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(address);

    return dereference_if(if_expr, offset, type);
  }
  else if(address.id()==ID_constant)
  {
    const typet result_type=ns.follow(address.type()).subtype();

    // pointer-typed constant
    if(to_constant_expr(address).get_value()==ID_NULL) // NULL
    {
      // we turn this into (type *)0
      exprt zero=from_integer(0, index_type());
      return dereference_rec(
        typecast_exprt(zero, address.type()), offset, type);
    }
    else
      throw "dereferencet: unexpected pointer constant "+address.pretty();
  }
  else
  {
    throw "failed to dereference `"+address.id_string()+"'";
  }
}

/// Attempt to dereference the object at address `expr + offset` and of
/// type `type`. Throws an exception if unsuccessful.
///
/// This is done by dereferencing both the true and false cases of the if
/// expression and putting the result together in a new if expression with the
/// same condition.
/// \return the dereferenced object
exprt dereferencet::dereference_if(
  const if_exprt &expr,
  const exprt &offset,
  const typet &type)
{
  // push down the if, do recursive call
  exprt true_case=dereference_rec(expr.true_case(), offset, type);
  exprt false_case=dereference_rec(expr.false_case(), offset, type);

  return if_exprt(expr.cond(), true_case, false_case);
}

/// Attempt to dereference the object at address `expr + offset` and of
/// type `type`. Throws an exception if unsuccessful. This assumes `expr` is
/// a `plus_exprt` but does not check for it.
exprt dereferencet::dereference_plus(
  const exprt &expr,
  const exprt &offset,
  const typet &type)
{
  exprt pointer=expr.op0();
  exprt integer=expr.op1();

  // need not be binary
  if(expr.operands().size()>2)
  {
    assert(expr.op0().type().id()==ID_pointer);

    exprt::operandst plus_ops(
      ++expr.operands().begin(), expr.operands().end());
    integer.operands().swap(plus_ops);
  }

  if(ns.follow(integer.type()).id()==ID_pointer)
    std::swap(pointer, integer);

  // multiply integer by object size
  exprt size=size_of_expr(pointer.type().subtype(), ns);
  if(size.is_nil())
    throw "dereference failed to get object size for pointer arithmetic";

  // make types of offset and size match
  if(size.type()!=integer.type())
    integer.make_typecast(size.type());

  const plus_exprt new_offset(offset, mult_exprt(size, integer));

  return dereference_rec(pointer, new_offset, type);
}

/// Attempt to dereference the object at address `expr + offset` and of
/// type `type`. Throws an exception if unsuccessful.
///
/// If `expr` is a typecast of the form `(type)ptr`:
///   - if `ptr` is of pointer type, dereference `ptr + offset`
///   - if `ptr` is of integer type, return an integer_dereference expression
///   - otherwise throw an exception
/// \return The dereferenced object.
exprt dereferencet::dereference_typecast(
  const typecast_exprt &expr,
  const exprt &offset,
  const typet &type)
{
  const exprt &op=expr.op();
  const typet &op_type=ns.follow(op.type());

  // pointer type cast?
  if(op_type.id()==ID_pointer)
    return dereference_rec(op, offset, type); // just pass down
  else if(op_type.id()==ID_signedbv || op_type.id()==ID_unsignedbv)
  {
    // We got an integer-typed address A. We turn this
    // into integer_dereference(A+offset),
    // and then let some other layer worry about it.

    exprt integer=op;

    if(!offset.is_zero())
      integer=
        plus_exprt(offset, typecast_exprt(op, offset.type()));

    return unary_exprt(ID_integer_dereference, integer, type);
  }
  else
    throw "dereferencet: unexpected cast";
}

/// Check that it is ok to cast an object of type `object_type` to
/// `deference_type`.
bool dereferencet::type_compatible(
  const typet &object_type,
  const typet &dereference_type) const
{
  if(dereference_type.id()==ID_empty)
    return true; // always ok

  if(base_type_eq(object_type, dereference_type, ns))
    return true; // ok, they just match

  // check for struct prefixes

  if(object_type.id()==ID_struct &&
     dereference_type.id()==ID_struct)
  {
    if(to_struct_type(dereference_type).is_prefix_of(
         to_struct_type(object_type)))
      return true; // ok, dereference_type is a prefix of object_type
  }

  // any code is ok
  if(dereference_type.id()==ID_code &&
     object_type.id()==ID_code)
    return true;

  // bit vectors of same size are ok
  if((object_type.id()==ID_signedbv || object_type.id()==ID_unsignedbv) &&
     (dereference_type.id()==ID_signedbv ||
      dereference_type.id()==ID_unsignedbv))
  {
    return object_type.get(ID_width)==dereference_type.get(ID_width);
  }

  // Any pointer to pointer is always ok,
  // but should likely check that width is the same.
  if(object_type.id()==ID_pointer &&
     dereference_type.id()==ID_pointer)
    return true;

  // really different

  return false;
}
