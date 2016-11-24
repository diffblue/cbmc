/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "arith_tools.h"
#include "byte_operators.h"
#include "config.h"
#include "namespace.h"
#include "pointer_offset_size.h"
#include "i2string.h"

#include "std_types.h"
#include "std_expr.h"

/*******************************************************************\

Function: constant_exprt::value_is_zero_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool constant_exprt::value_is_zero_string() const
{
  const std::string val=id2string(get_value());
  return val.find_first_not_of('0')==std::string::npos;
}

/*******************************************************************\

Function: disjunction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt disjunction(const exprt::operandst &op)
{
  if(op.empty())
    return false_exprt();
  else if(op.size()==1)
    return op.front();
  else
  {
    or_exprt result;
    result.operands()=op;
    return result;
  }
}

/*******************************************************************\

Function: conjunction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt conjunction(const exprt::operandst &op)
{
  if(op.empty())
    return true_exprt();
  else if(op.size()==1)
    return op.front();
  else
  {
    and_exprt result;
    result.operands()=op;
    return result;
  }
}

/*******************************************************************\

Function: build_object_descriptor_rec

  Inputs:

 Outputs:

 Purpose: Build an object_descriptor_exprt from a given expr

\*******************************************************************/

static void build_object_descriptor_rec(
  const namespacet &ns,
  const exprt &expr,
  object_descriptor_exprt &dest)
{
  const signedbv_typet index_type(config.ansi_c.pointer_width);

  if(expr.id()==ID_index)
  {
    const index_exprt &index=to_index_expr(expr);

    build_object_descriptor_rec(ns, index.array(), dest);

    exprt sub_size=size_of_expr(expr.type(), ns);
    assert(sub_size.is_not_nil());

    dest.offset()=
      plus_exprt(dest.offset(),
                 mult_exprt(typecast_exprt(index.index(), index_type),
                            typecast_exprt(sub_size, index_type)));
  }
  else if(expr.id()==ID_member)
  {
    const member_exprt &member=to_member_expr(expr);
    const exprt &struct_op=member.struct_op();
    const typet &struct_type=ns.follow(struct_op.type());

    build_object_descriptor_rec(ns, struct_op, dest);

    if(struct_type.id()==ID_union)
      return;

    mp_integer offset=
      member_offset(to_struct_type(struct_type),
                    member.get_component_name(), ns);
    assert(offset>=0);

    dest.offset()=
      plus_exprt(dest.offset(), from_integer(offset, index_type));
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    const byte_extract_exprt &be=to_byte_extract_expr(expr);

    dest.object()=be.op();

    build_object_descriptor_rec(ns, be.op(), dest);

    dest.offset()=
      plus_exprt(dest.offset(),
                 typecast_exprt(to_byte_extract_expr(expr).offset(),
                                index_type));
  }
}

/*******************************************************************\

Function: object_descriptor_exprt::build

  Inputs:

 Outputs:

 Purpose: Build an object_descriptor_exprt from a given expr

\*******************************************************************/

void object_descriptor_exprt::build(
  const exprt &expr,
  const namespacet &ns)
{
  assert(object().id()==ID_unknown);
  object()=expr;

  if(offset().id()==ID_unknown)
    offset()=from_integer(0, signedbv_typet(config.ansi_c.pointer_width));

  build_object_descriptor_rec(ns, expr, *this);

  assert(root_object().type().id()!=ID_empty);
}

/*******************************************************************\

Function: constant_exprt::integer_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt constant_exprt::integer_constant(unsigned v)
{
  return constant_exprt(i2string(v), integer_typet());
}

/*******************************************************************\

Function: shift_exprt::shift_exprt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

shift_exprt::shift_exprt(
  const exprt &_src,
  const irep_idt &_id,
  const unsigned _distance):
  binary_exprt(_src, _id, constant_exprt::integer_constant(_distance))
{
}

/*******************************************************************\

Function: extractbit_exprt::extractbit_exprt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

extractbit_exprt::extractbit_exprt(
  const exprt &_src,
  const unsigned _index):
  binary_predicate_exprt(
    _src, ID_extractbit, constant_exprt::integer_constant(_index))
{
}

/*******************************************************************\

Function: extractbit_exprt::extractbits_exprt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

extractbits_exprt::extractbits_exprt(
  const exprt &_src,
  const unsigned _upper,
  const unsigned _lower,
  const typet &_type):
  exprt(ID_extractbits, _type)
{
  assert(_upper>=_lower);
  operands().resize(3);
  src()=_src;
  upper()=constant_exprt::integer_constant(_upper);
  lower()=constant_exprt::integer_constant(_lower);
}

