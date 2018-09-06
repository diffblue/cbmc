/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "std_expr.h"

#include <util/namespace.h>

#include <cassert>

#include "arith_tools.h"
#include "byte_operators.h"
#include "c_types.h"
#include "pointer_offset_size.h"

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
    CHECK_RETURN(sub_size.is_not_nil());

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
    CHECK_RETURN(offset.is_not_nil());

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
  PRECONDITION(object().id() == ID_unknown);
  object()=expr;

  if(offset().id()==ID_unknown)
    offset()=from_integer(0, index_type());

  build_object_descriptor_rec(ns, expr, *this);

  POSTCONDITION(root_object().type().id() != ID_empty);
}

shift_exprt::shift_exprt(
  const exprt &_src,
  const irep_idt &_id,
  const std::size_t _distance):
  binary_exprt(_src, _id, from_integer(_distance, integer_typet()))
{
}

extractbit_exprt::extractbit_exprt(
  const exprt &_src,
  const std::size_t _index):
  binary_predicate_exprt(
    _src, ID_extractbit, from_integer(_index, integer_typet()))
{
}

extractbits_exprt::extractbits_exprt(
  const exprt &_src,
  const std::size_t _upper,
  const std::size_t _lower,
  const typet &_type):
  exprt(ID_extractbits, _type)
{
  PRECONDITION(_upper >= _lower);
  operands().resize(3);
  src()=_src;
  upper()=from_integer(_upper, integer_typet());
  lower()=from_integer(_lower, integer_typet());
}

address_of_exprt::address_of_exprt(const exprt &_op):
  unary_exprt(ID_address_of, _op, pointer_type(_op.type()))
{
}

// Implementation of struct_exprt::component for const / non const overloads.
template <typename T>
auto component(T &struct_expr, const irep_idt &name, const namespacet &ns)
  -> decltype(struct_expr.op0())
{
  static_assert(
    std::is_base_of<struct_exprt, T>::value, "T must be a struct_exprt.");
  const auto index =
    to_struct_type(ns.follow(struct_expr.type())).component_number(name);
  DATA_INVARIANT(
    index < struct_expr.operands().size(),
    "component matching index should exist");
  return struct_expr.operands()[index];
}

/// \return The expression for a named component of this struct.
exprt &struct_exprt::component(const irep_idt &name, const namespacet &ns)
{
  return ::component(*this, name, ns);
}

/// \return The expression for a named component of this struct.
const exprt &
struct_exprt::component(const irep_idt &name, const namespacet &ns) const
{
  return ::component(*this, name, ns);
}

const exprt &object_descriptor_exprt::root_object() const
{
  const exprt *p = &object();

  while(p->id() == ID_member || p->id() == ID_index)
  {
    DATA_INVARIANT(
      p->has_operands(), "member and index expressions have operands");
    p = &p->op0();
  }

  return *p;
}
