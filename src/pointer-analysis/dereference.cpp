/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "dereference.h"

#ifdef DEBUG
static int deref_depth=0;
#include <iostream>
#include <langapi/language_util.h>
#endif

#include <util/std_expr.h>
#include <util/byte_operators.h>
#include <util/pointer_offset_size.h>
#include <util/base_type.h>
#include <util/simplify_expr.h>
#include <util/arith_tools.h>
#include <util/namespace.h>
#include <util/cprover_prefix.h>
#include <util/symbol.h>
#include <util/config.h>

#include <util/c_types.h>

// #define USE_NULL_OBJECT

/// Build byte_extract_* for the given root object and offset
static exprt build_byte_extract(
  const namespacet &ns,
  const exprt &object,
  const exprt &offset,
  const typet &type)
{
  if(object.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(object);

    exprt true_case=
      build_byte_extract(ns, if_expr.true_case(), offset, type);

    exprt false_case=
      build_byte_extract(ns, if_expr.false_case(), offset, type);

    return if_exprt(if_expr.cond(), true_case, false_case);
  }

  object_descriptor_exprt ode;
  ode.offset()=offset;
  ode.build(object, ns);

  byte_extract_exprt be(byte_extract_id());
  be.type()=type;
  be.op()=ode.root_object();
  CHECK_RETURN(be.op().is_not_nil());
  be.offset()=ode.offset();

  return simplify_expr(be, ns);
}

/// Test whether type is char*, void*, or an integer type
static bool is_generic_pointer_type(
  const namespacet &ns,
  const typet &type)
{
  return
    base_type_eq(type, pointer_type(empty_typet()), ns) ||
    base_type_eq(type, pointer_type(char_type()), ns) ||
    type.id()==ID_signedbv || type.id()==ID_unsignedbv;
}

/// Returns true, iff some operand has pointer type
static bool has_pointer(const exprt &expr, const namespacet &ns)
{
  if(ns.follow(expr.type()).id()==ID_pointer)
    return true;

  forall_operands(it, expr)
    if(has_pointer(*it, ns))
      return true;

  return false;
}

/// \par parameters: expression, to be dereferenced
/// \return returns object after dereferencing
exprt dereferencet::operator()(
  const exprt &pointer,
  exprt &invalid_cond)
{
  if(pointer.type().id()!=ID_pointer)
    throw "dereference expected pointer type, but got "+
          pointer.type().pretty();

  // type of the object
  const typet &type=ns.follow(pointer.type()).subtype();

  // we don't deal with { array }[index], { struct }.member - let
  // simplify worry about these
  const exprt simp_pointer=simplify_expr(pointer, ns);

  #ifdef DEBUG
  std::cout << "DEREF: " << from_expr(ns, "", simp_pointer) << '\n';
  #endif

  // recursively push down the dereferencing operator

  invalid_cond=false_exprt();
  return dereference_rec(
    simp_pointer,
    from_integer(0, index_type()), // offset
    type,
    invalid_cond);
}

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

    exprt new_offset=plus_exprt(simplified_offset, mult_exprt(index, size));

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

      exprt new_offset=plus_exprt(simplified_offset, member_offset);

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
  return build_byte_extract(ns, object, simplified_offset, dest_type);
}

/// Compute *expr
exprt dereferencet::dereference_rec(
  const exprt &address,
  const exprt &offset,
  const typet &type,
  exprt &invalid_cond)
{
#ifdef DEBUG
  std::cerr << std::string(2*deref_depth, ' ') << deref_depth
            << ": deref_rec: " << from_expr(ns, "", address) << '\n';
  ++deref_depth;
#endif

  const typet &expr_type=ns.follow(address.type());
  exprt result=nil_exprt();

  // the base case: we arrived at &object
  if(address.id()==ID_address_of)
  {
    const address_of_exprt &address_of_expr=to_address_of_expr(address);

    const exprt &object=address_of_expr.object();

    if(object.id()==ID_if)
    {
      const if_exprt &if_expr=to_if_expr(object);

      if_exprt new_if(
        if_expr.cond(),
        address_of_exprt(if_expr.true_case()),
        address_of_exprt(if_expr.false_case()));

      result=dereference_rec(new_if, offset, type, invalid_cond);
    }
    else
      result=read_object(object, offset, type);
  }
  // *((T) x)
  else if(address.id()==ID_typecast)
  {
    const typecast_exprt &typecast_expr=to_typecast_expr(address);

    result=dereference_typecast(
      typecast_expr,
      offset,
      type,
      invalid_cond);
  }
  // *(p + c)
  else if(address.id()==ID_plus)
  {
    // pointer arithmetic
    if(address.operands().size()<2)
      throw "plus with less than two operands";

    PRECONDITION(
      expr_type.id()==ID_pointer ||
      is_generic_pointer_type(ns, expr_type));
    result=dereference_plus(address, offset, type, invalid_cond);
  }
  // *(c ? x : y)
  else if(address.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(address);

    result=dereference_if(if_expr, offset, type, invalid_cond);
  }
#if 0
  // consider handling further cases, such as bitmasks
  else if(address.id()==ID_bitand)
  {
    // just ignores the (negative) offset induced by bitand
    // TODO: more precision
    forall_operands(it, address)
      if(has_pointer(*it, ns))
      {
        result=dereference_rec(*it, offset, type, invalid_cond);
        break;
      }
  }
#endif
  // NULL pointer dereference
  else if((address.is_constant() &&
           to_constant_expr(address).get_value()==ID_NULL) ||
          (config.ansi_c.NULL_is_zero &&
           (expr_type.id()==ID_unsignedbv ||
            expr_type.id()==ID_signedbv) &&
           simplify_expr(address, ns).is_zero()))
  {
#ifdef USE_NULL_OBJECT
      result=exprt("NULL-object", type);
#else
      invalid_cond.make_true();
#endif
  }
  // *c for some integer expression
  else if(expr_type.id()==ID_unsignedbv ||
          expr_type.id()==ID_signedbv)
  {
    exprt symbol_expr=ns.lookup(CPROVER_PREFIX "memory").symbol_expr();

    byte_extract_exprt be(byte_extract_id());
    be.type()=type;
    be.op()=symbol_expr;
    be.offset()=address;
    if(!base_type_eq(be.offset().type(), index_type(), ns))
      be.offset().make_typecast(index_type());

    result=be;
  }
  else
    // anything else is definitively invalid
    invalid_cond.make_true();

#ifdef DEBUG
  --deref_depth;
  std::cerr << std::string(2*deref_depth, ' ') << deref_depth << ": deref_rec "
    << address.id() << " result cand: "
    << "{g=" << from_expr(ns, "", not_exprt(invalid_cond)) << "} "
    << from_expr(ns, "", result) << '\n';
#endif

  return result;
}

/// Compute *(c ? x : y) via c ? *x : *y
exprt dereferencet::dereference_if(
  const if_exprt &expr,
  const exprt &offset,
  const typet &type,
  exprt &invalid_cond)
{
  // push down the if, do recursive call

  exprt t_inv=false_exprt();
  exprt true_case=
    dereference_rec(expr.true_case(), offset, type, t_inv);

  exprt f_inv=false_exprt();
  exprt false_case=
    dereference_rec(expr.false_case(), offset, type, f_inv);

  if(t_inv.is_true())
  {
    invalid_cond=or_exprt(expr.cond(), f_inv);
    simplify(invalid_cond, ns);

    return false_case;
  }
  else if(f_inv.is_true())
  {
    invalid_cond=or_exprt(not_exprt(expr.cond()), t_inv);
    simplify(invalid_cond, ns);

    return true_case;
  }
  else if(t_inv.is_false() && !f_inv.is_false())
  {
    invalid_cond=and_exprt(not_exprt(expr.cond()), f_inv);
  }
  else if(!t_inv.is_false() && f_inv.is_false())
  {
    invalid_cond=and_exprt(expr.cond(), t_inv);
  }
  else if(!t_inv.is_false() || !f_inv.is_false())
  {
    invalid_cond=
      and_exprt(
        or_exprt(expr.cond(), and_exprt(not_exprt(t_inv), f_inv)),
        or_exprt(not_exprt(expr.cond()), and_exprt(t_inv, not_exprt(f_inv))));
  }

  simplify(invalid_cond, ns);

  return if_exprt(expr.cond(), true_case, false_case);
}

/// Compute *(p + c) for a pointer p and an integer c
exprt dereferencet::dereference_plus(
  const exprt &expr,
  const exprt &offset,
  const typet &type,
  exprt &invalid_cond)
{
  exprt pointer=expr.op0();
  exprt integer=expr.op1();

  // need not be binary
  if(expr.operands().size()>2)
  {
    PRECONDITION(expr.op0().type().id()==ID_pointer);

    exprt::operandst plus_ops(
      ++expr.operands().begin(), expr.operands().end());
    integer.operands().swap(plus_ops);
  }

  if(has_pointer(integer, ns) &&
     (pointer.type().id()!=ID_pointer ||
      integer.type().id()==ID_pointer))
  {
    if(has_pointer(pointer, ns))
      throw "unsupported pointer arithmetic using sum of pointers";

    std::swap(pointer, integer);
  }
  else if(!has_pointer(pointer, ns))
  {
    invalid_cond.make_true();
    return nil_exprt();
  }

  exprt size=size_of_expr(char_type(), ns);
  CHECK_RETURN(size.is_not_nil());

  // make types of offset and size match
  if(size.type()!=integer.type())
    integer.make_typecast(size.type());

  if(ns.follow(pointer.type()).id()==ID_pointer)
  {
    const typet &object_type=ns.follow(pointer.type()).subtype();
    if(object_type.id()!=ID_empty)
      size=size_of_expr(object_type, ns);

    if(size.is_nil())
      throw "dereference failed to get object size for pointer arithmetic";
  }
  else if(pointer.id()==ID_typecast)
  {
    pointer=to_typecast_expr(pointer).op();
  }

  // multiply integer by object size
  exprt new_offset=plus_exprt(offset, mult_exprt(size, integer));

  return dereference_rec(pointer, new_offset, type, invalid_cond);
}

/// Compute *((T)x)
exprt dereferencet::dereference_typecast(
  const typecast_exprt &expr,
  const exprt &offset,
  const typet &type,
  exprt &invalid_cond)
{
  const typet &expr_type=ns.follow(expr.type());
  const exprt &op=expr.op();
  const typet &op_type=ns.follow(op.type());

  // pointer type cast?
  if(op_type.id()==ID_pointer &&
     expr_type.id()==ID_pointer)
  {
    exprt result;

    // typecast from generic pointer type
    if(is_generic_pointer_type(ns, op_type))
      result=dereference_rec(op, offset, type, invalid_cond);
    else
      result=dereference_rec(op, offset, op_type.subtype(), invalid_cond);

    if(invalid_cond.is_true())
      return result;

    typet extract_type=type;
    // typecast to a generic pointer type
    if(is_generic_pointer_type(ns, expr_type) &&
       !is_generic_pointer_type(ns, op_type) &&
       !is_generic_pointer_type(ns, pointer_type(type)))
      extract_type=op_type.subtype();

    // zero extra offset
    const exprt offset=exprt(ID_unknown);
    return build_byte_extract(ns, result, offset, extract_type);
  }
  // integer-to-pointer or something-to-integer
  else if((expr_type.id()==ID_pointer &&
           (op_type.id()==ID_unsignedbv ||
            op_type.id()==ID_signedbv)) ||
          expr_type.id()==ID_unsignedbv ||
          expr_type.id()==ID_signedbv)
  {
    // we can no longer rely on a sane relation of types
    return dereference_rec(op, offset, type, invalid_cond);
  }
  else
    throw "dereferencet: unexpected cast";
}

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
