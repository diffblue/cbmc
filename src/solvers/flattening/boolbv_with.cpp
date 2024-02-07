/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/c_types.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include "boolbv.h"

bvt boolbvt::convert_with(const with_exprt &expr)
{
  auto &type = expr.type();

  if(
    type.id() == ID_bv || type.id() == ID_unsignedbv ||
    type.id() == ID_signedbv)
  {
    if(expr.operands().size() > 3)
    {
      std::size_t s = expr.operands().size();

      // strip off the trailing two operands
      with_exprt tmp = expr;
      tmp.operands().resize(s - 2);

      with_exprt new_with_expr(
        tmp, expr.operands()[s - 2], expr.operands().back());

      // recursive call
      return convert_with(new_with_expr);
    }

    PRECONDITION(expr.operands().size() == 3);
    if(expr.new_value().type().id() == ID_bool)
    {
      return convert_bv(
        update_bit_exprt(expr.old(), expr.where(), expr.new_value()));
    }
    else
    {
      return convert_bv(
        update_bits_exprt(expr.old(), expr.where(), expr.new_value()));
    }
  }

  bvt bv = convert_bv(expr.old());

  std::size_t width = boolbv_width(type);

  if(width==0)
  {
    // A zero-length array is acceptable:
    return bvt{};
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
  const exprt &where,
  const exprt &new_value,
  const bvt &prev_bv,
  bvt &next_bv)
{
  // we only do that on arrays, bitvectors, structs, and unions

  next_bv.resize(prev_bv.size());

  if(type.id()==ID_array)
    return convert_with_array(
      to_array_type(type), where, new_value, prev_bv, next_bv);
  else if(type.id()==ID_bv ||
          type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv)
  {
    // already done
    PRECONDITION(false);
  }
  else if(type.id()==ID_struct)
    return convert_with_struct(
      to_struct_type(type), where, new_value, prev_bv, next_bv);
  else if(type.id() == ID_struct_tag)
    return convert_with(
      ns.follow_tag(to_struct_tag_type(type)),
      where,
      new_value,
      prev_bv,
      next_bv);
  else if(type.id()==ID_union)
    return convert_with_union(to_union_type(type), new_value, prev_bv, next_bv);
  else if(type.id() == ID_union_tag)
    return convert_with(
      ns.follow_tag(to_union_tag_type(type)),
      where,
      new_value,
      prev_bv,
      next_bv);

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    false, "unexpected with type", irep_pretty_diagnosticst{type});
}

void boolbvt::convert_with_array(
  const array_typet &type,
  const exprt &index,
  const exprt &new_value,
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

  const bvt &new_value_bv = convert_bv(new_value);

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    *size * new_value_bv.size() == prev_bv.size(),
    "convert_with_array: unexpected new_value operand width",
    irep_pretty_diagnosticst{type});

  // Is the index a constant?
  if(const auto index_value_opt = numeric_cast<mp_integer>(index))
  {
    // Yes, it is!
    next_bv=prev_bv;

    if(*index_value_opt >= 0 && *index_value_opt < *size) // bounds check
    {
      const std::size_t offset =
        numeric_cast_v<std::size_t>(*index_value_opt * new_value_bv.size());

      for(std::size_t j = 0; j < new_value_bv.size(); j++)
        next_bv[offset + j] = new_value_bv[j];
    }

    return;
  }

  typet counter_type = index.type();

  for(mp_integer i=0; i<size; i=i+1)
  {
    exprt counter=from_integer(i, counter_type);

    literalt eq_lit = convert(equal_exprt(index, counter));

    const std::size_t offset =
      numeric_cast_v<std::size_t>(i * new_value_bv.size());

    for(std::size_t j = 0; j < new_value_bv.size(); j++)
      next_bv[offset + j] =
        prop.lselect(eq_lit, new_value_bv[j], prev_bv[offset + j]);
  }
}

void boolbvt::convert_with_struct(
  const struct_typet &type,
  const exprt &where,
  const exprt &new_value,
  const bvt &prev_bv,
  bvt &next_bv)
{
  next_bv=prev_bv;

  const bvt &new_value_bv = convert_bv(new_value);

  const irep_idt &component_name = where.get(ID_component_name);
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
        subtype == new_value.type(),
        "with/struct: component '" + id2string(component_name) +
          "' type does not match",
        irep_pretty_diagnosticst{subtype},
        irep_pretty_diagnosticst{new_value.type()});

      DATA_INVARIANT_WITH_DIAGNOSTICS(
        sub_width == new_value_bv.size(),
        "convert_with_struct: unexpected new_value operand width",
        irep_pretty_diagnosticst{type});

      for(std::size_t i=0; i<sub_width; i++)
        next_bv[offset + i] = new_value_bv[i];

      break; // done
    }

    offset+=sub_width;
  }
}

void boolbvt::convert_with_union(
  const union_typet &type,
  const exprt &new_value,
  const bvt &prev_bv,
  bvt &next_bv)
{
  next_bv=prev_bv;

  const bvt &new_value_bv = convert_bv(new_value);

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    next_bv.size() >= new_value_bv.size(),
    "convert_with_union: unexpected new_value operand width",
    irep_pretty_diagnosticst{type});

  endianness_mapt map_u = endianness_map(type);
  endianness_mapt map_new_value = endianness_map(new_value.type());

  for(std::size_t i = 0; i < new_value_bv.size(); i++)
    next_bv[map_u.map_bit(i)] = new_value_bv[map_new_value.map_bit(i)];
}
