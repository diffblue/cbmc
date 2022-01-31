/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/namespace.h>
#include <util/std_expr.h>

bvt boolbvt::convert_with(const with_exprt &expr)
{
  bvt bv = convert_bv(expr.old());

  std::size_t width=boolbv_width(expr.type());

  if(width==0)
  {
    // A zero-length array is acceptable:
    if(
      expr.type().id() == ID_array &&
      boolbv_width(to_array_type(expr.type()).element_type()) != 0)
    {
      return bvt();
    }
    else
      return conversion_failed(expr);
  }

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    bv.size() == width,
    "unexpected operand 0 width",
    irep_pretty_diagnosticst{expr});

  bvt prev_bv;
  prev_bv.resize(width);

  const exprt::operandst &ops=expr.operands();

  for(std::size_t op_no=1; op_no<ops.size(); op_no+=2)
  {
    bv.swap(prev_bv);

    convert_with(expr.old().type(), ops[op_no], ops[op_no + 1], prev_bv, bv);
  }

  return bv;
}

void boolbvt::convert_with(
  const typet &type,
  const exprt &op1,
  const exprt &op2,
  const bvt &prev_bv,
  bvt &next_bv)
{
  // we only do that on arrays, bitvectors, structs, and unions

  next_bv.resize(prev_bv.size());

  if(type.id()==ID_array)
    return convert_with_array(to_array_type(type), op1, op2, prev_bv, next_bv);
  else if(type.id()==ID_bv ||
          type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv)
    return convert_with_bv(op1, op2, prev_bv, next_bv);
  else if(type.id()==ID_struct)
    return
      convert_with_struct(to_struct_type(type), op1, op2, prev_bv, next_bv);
  else if(type.id() == ID_struct_tag)
    return convert_with(
      ns.follow_tag(to_struct_tag_type(type)), op1, op2, prev_bv, next_bv);
  else if(type.id()==ID_union)
    return convert_with_union(to_union_type(type), op2, prev_bv, next_bv);
  else if(type.id() == ID_union_tag)
    return convert_with(
      ns.follow_tag(to_union_tag_type(type)), op1, op2, prev_bv, next_bv);

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    false, "unexpected with type", irep_pretty_diagnosticst{type});
}

void boolbvt::convert_with_array(
  const array_typet &type,
  const exprt &op1,
  const exprt &op2,
  const bvt &prev_bv,
  bvt &next_bv)
{
  // can't do this
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    !is_unbounded_array(type),
    "convert_with_array called for unbounded array",
    irep_pretty_diagnosticst{type});

  const exprt &array_size=type.size();

  const auto size = numeric_cast<mp_integer>(array_size);

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    size.has_value(),
    "convert_with_array expects constant array size",
    irep_pretty_diagnosticst{type});

  const bvt &op2_bv=convert_bv(op2);

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    *size * op2_bv.size() == prev_bv.size(),
    "convert_with_array: unexpected operand 2 width",
    irep_pretty_diagnosticst{type});

  // Is the index a constant?
  if(const auto op1_value = numeric_cast<mp_integer>(op1))
  {
    // Yes, it is!
    next_bv=prev_bv;

    if(*op1_value >= 0 && *op1_value < *size) // bounds check
    {
      const std::size_t offset =
        numeric_cast_v<std::size_t>(*op1_value * op2_bv.size());

      for(std::size_t j=0; j<op2_bv.size(); j++)
        next_bv[offset+j]=op2_bv[j];
    }

    return;
  }

  typet counter_type=op1.type();

  for(mp_integer i=0; i<size; i=i+1)
  {
    exprt counter=from_integer(i, counter_type);

    literalt eq_lit=convert(equal_exprt(op1, counter));

    const std::size_t offset = numeric_cast_v<std::size_t>(i * op2_bv.size());

    for(std::size_t j=0; j<op2_bv.size(); j++)
      next_bv[offset+j]=
        prop.lselect(eq_lit, op2_bv[j], prev_bv[offset+j]);
  }
}

void boolbvt::convert_with_bv(
  const exprt &op1,
  const exprt &op2,
  const bvt &prev_bv,
  bvt &next_bv)
{
  literalt l=convert(op2);

  if(const auto op1_value = numeric_cast<mp_integer>(op1))
  {
    next_bv=prev_bv;

    if(*op1_value < next_bv.size())
      next_bv[numeric_cast_v<std::size_t>(*op1_value)] = l;

    return;
  }

  typet counter_type=op1.type();

  for(std::size_t i=0; i<prev_bv.size(); i++)
  {
    exprt counter=from_integer(i, counter_type);

    literalt eq_lit=convert(equal_exprt(op1, counter));

    next_bv[i]=prop.lselect(eq_lit, l, prev_bv[i]);
  }
}

void boolbvt::convert_with_struct(
  const struct_typet &type,
  const exprt &op1,
  const exprt &op2,
  const bvt &prev_bv,
  bvt &next_bv)
{
  next_bv=prev_bv;

  const bvt &op2_bv=convert_bv(op2);

  const irep_idt &component_name=op1.get(ID_component_name);
  const struct_typet::componentst &components=
    type.components();

  std::size_t offset=0;

  for(const auto &c : components)
  {
    const typet &subtype = c.type();

    std::size_t sub_width=boolbv_width(subtype);

    if(c.get_name() == component_name)
    {
      DATA_INVARIANT_WITH_DIAGNOSTICS(
        subtype == op2.type(),
        "with/struct: component '" + id2string(component_name) +
          "' type does not match",
        irep_pretty_diagnosticst{subtype},
        irep_pretty_diagnosticst{op2.type()});

      DATA_INVARIANT_WITH_DIAGNOSTICS(
        sub_width == op2_bv.size(),
        "convert_with_struct: unexpected operand op2 width",
        irep_pretty_diagnosticst{type});

      for(std::size_t i=0; i<sub_width; i++)
        next_bv[offset+i]=op2_bv[i];

      break; // done
    }

    offset+=sub_width;
  }
}

void boolbvt::convert_with_union(
  const union_typet &type,
  const exprt &op2,
  const bvt &prev_bv,
  bvt &next_bv)
{
  next_bv=prev_bv;

  const bvt &op2_bv=convert_bv(op2);

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    next_bv.size() >= op2_bv.size(),
    "convert_with_union: unexpected operand op2 width",
    irep_pretty_diagnosticst{type});

  endianness_mapt map_u = endianness_map(type);
  endianness_mapt map_op2 = endianness_map(op2.type());

  for(std::size_t i = 0; i < op2_bv.size(); i++)
    next_bv[map_u.map_bit(i)] = op2_bv[map_op2.map_bit(i)];
}
