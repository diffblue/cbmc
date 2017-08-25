/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "std_expr.h"

#include <cassert>

#include "arith_tools.h"
#include "byte_operators.h"
#include "c_types.h"
#include "namespace.h"
#include "pointer_offset_size.h"
#include "std_types.h"

bool constant_exprt::value_is_zero_string() const
{
  const std::string val=id2string(get_value());
  return val.find_first_not_of('0')==std::string::npos;
}

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

void dynamic_object_exprt::set_instance(unsigned int instance)
{
  op0()=from_integer(instance, typet(ID_natural));
}

unsigned int dynamic_object_exprt::get_instance() const
{
  return std::stoul(id2string(to_constant_expr(op0()).get_value()));
}

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

/// Build an object_descriptor_exprt from a given expr
static void build_object_descriptor_rec(
  const namespacet &ns,
  const exprt &expr,
  object_descriptor_exprt &dest)
{
  if(expr.id()==ID_index)
  {
    const index_exprt &index=to_index_expr(expr);

    build_object_descriptor_rec(ns, index.array(), dest);

    exprt sub_size=size_of_expr(expr.type(), ns);
    assert(sub_size.is_not_nil());

    dest.offset()=
      plus_exprt(dest.offset(),
                 mult_exprt(typecast_exprt(index.index(), index_type()),
                            typecast_exprt(sub_size, index_type())));
  }
  else if(expr.id()==ID_member)
  {
    const member_exprt &member=to_member_expr(expr);
    const exprt &struct_op=member.struct_op();

    build_object_descriptor_rec(ns, struct_op, dest);

    exprt offset=member_offset_expr(member, ns);
    assert(offset.is_not_nil());

    dest.offset()=
      plus_exprt(dest.offset(),
                 typecast_exprt(offset, index_type()));
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
                                index_type()));
  }
  else if(expr.id()==ID_typecast)
  {
    const typecast_exprt &tc=to_typecast_expr(expr);

    dest.object()=tc.op();

    build_object_descriptor_rec(ns, tc.op(), dest);
  }
}

/// Build an object_descriptor_exprt from a given expr
void object_descriptor_exprt::build(
  const exprt &expr,
  const namespacet &ns)
{
  assert(object().id()==ID_unknown);
  object()=expr;

  if(offset().id()==ID_unknown)
    offset()=from_integer(0, index_type());

  build_object_descriptor_rec(ns, expr, *this);

  assert(root_object().type().id()!=ID_empty);
}

static constant_exprt integer_constant(unsigned v)
{
  return constant_exprt(std::to_string(v), integer_typet());
}

shift_exprt::shift_exprt(
  const exprt &_src,
  const irep_idt &_id,
  const std::size_t _distance):
  binary_exprt(_src, _id, integer_constant(_distance))
{
}

extractbit_exprt::extractbit_exprt(
  const exprt &_src,
  const std::size_t _index):
  binary_predicate_exprt(
    _src, ID_extractbit, integer_constant(_index))
{
}

extractbits_exprt::extractbits_exprt(
  const exprt &_src,
  const std::size_t _upper,
  const std::size_t _lower,
  const typet &_type):
  exprt(ID_extractbits, _type)
{
  assert(_upper>=_lower);
  operands().resize(3);
  src()=_src;
  upper()=integer_constant(_upper);
  lower()=integer_constant(_lower);
}

address_of_exprt::address_of_exprt(const exprt &_op):
  unary_exprt(ID_address_of, _op, pointer_type(_op.type()))
{
}
