/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/threeval.h>

#include "boolbv.h"
#include "boolbv_type.h"

exprt boolbvt::get(const exprt &expr) const
{
  if(expr.id()==ID_symbol ||
     expr.id()==ID_nondet_symbol)
  {
    const irep_idt &identifier=expr.get(ID_identifier);

    const auto map_entry_opt = map.get_map_entry(identifier);

    if(map_entry_opt.has_value())
    {
      const boolbv_mapt::map_entryt &map_entry = *map_entry_opt;
      // an input expression must either be untyped (this is used for obtaining
      // the value of clock symbols, which do not have a fixed type as the clock
      // type is computed during symbolic execution) or match the type stored in
      // the mapping
      if(expr.type() == map_entry.type)
        return bv_get_rec(expr, map_entry.literal_map, 0);
      else
      {
        PRECONDITION(expr.type() == typet{});
        exprt skeleton = expr;
        skeleton.type() = map_entry.type;
        return bv_get_rec(skeleton, map_entry.literal_map, 0);
      }
    }
  }

  return SUB::get(expr);
}

exprt boolbvt::bv_get_rec(const exprt &expr, const bvt &bv, std::size_t offset)
  const
{
  const typet &type = expr.type();

  if(type.id()==ID_bool)
  {
    PRECONDITION(bv.size() > offset);
    // clang-format off
    switch(prop.l_get(bv[offset]).get_value())
    {
    case tvt::tv_enumt::TV_FALSE: return false_exprt();
    case tvt::tv_enumt::TV_TRUE:  return true_exprt();
    case tvt::tv_enumt::TV_UNKNOWN: return false_exprt(); // default
    }
    // clang-format on
  }

  bvtypet bvtype=get_bvtype(type);

  if(bvtype==bvtypet::IS_UNKNOWN)
  {
    if(type.id()==ID_array)
    {
      const auto &array_type = to_array_type(type);

      if(is_unbounded_array(type))
        return bv_get_unbounded_array(expr);

      const typet &subtype = array_type.element_type();
      const auto &sub_width_opt = bv_width.get_width_opt(subtype);

      if(sub_width_opt.has_value() && *sub_width_opt > 0)
      {
        const std::size_t width = boolbv_width(type);

        std::size_t sub_width = *sub_width_opt;

        exprt::operandst op;
        op.reserve(width/sub_width);

        for(std::size_t new_offset=0;
            new_offset<width;
            new_offset+=sub_width)
        {
          const index_exprt index{
            expr,
            from_integer(new_offset / sub_width, array_type.index_type())};
          op.push_back(bv_get_rec(index, bv, offset + new_offset));
        }

        exprt dest=exprt(ID_array, type);
        dest.operands().swap(op);
        return dest;
      }
      else
      {
        return array_exprt{{}, array_type};
      }
    }
    else if(type.id() == ID_struct || type.id() == ID_struct_tag)
    {
      const struct_typet::componentst &components =
        type.id() == ID_struct
          ? to_struct_type(type).components()
          : ns.follow_tag(to_struct_tag_type(type)).components();
      std::size_t new_offset=0;
      exprt::operandst op;
      op.reserve(components.size());

      for(const auto &c : components)
      {
        const typet &subtype = c.type();

        const member_exprt member{expr, c.get_name(), subtype};
        op.push_back(bv_get_rec(member, bv, offset + new_offset));

        new_offset += boolbv_width(subtype);
      }

      return struct_exprt(std::move(op), type);
    }
    else if(type.id() == ID_union || type.id() == ID_union_tag)
    {
      const union_typet::componentst &components =
        type.id() == ID_union
          ? to_union_type(type).components()
          : ns.follow_tag(to_union_tag_type(type)).components();

      if(components.empty())
        return empty_union_exprt(type);

      // Any idea that's better than just returning the first component?
      std::size_t component_nr=0;

      const typet &subtype = components[component_nr].type();

      const member_exprt member{
        expr, components[component_nr].get_name(), subtype};
      return union_exprt(
        components[component_nr].get_name(),
        bv_get_rec(member, bv, offset),
        type);
    }
    else if(type.id()==ID_vector)
    {
      const std::size_t width = boolbv_width(type);

      const auto &vector_type = to_vector_type(type);
      const typet &element_type = vector_type.element_type();
      std::size_t element_width = boolbv_width(element_type);
      CHECK_RETURN(element_width > 0);

      if(element_width != 0 && width % element_width == 0)
      {
        std::size_t size = width / element_width;
        vector_exprt value({}, vector_type);
        value.reserve_operands(size);

        for(std::size_t i=0; i<size; i++)
        {
          const index_exprt index{expr,
                                  from_integer(i, vector_type.index_type())};
          value.operands().push_back(bv_get_rec(index, bv, i * element_width));
        }

        return std::move(value);
      }
    }
    else if(type.id()==ID_complex)
    {
      const std::size_t width = boolbv_width(type);

      const typet &subtype = to_complex_type(type).subtype();
      const std::size_t sub_width = boolbv_width(subtype);
      CHECK_RETURN(sub_width > 0);
      DATA_INVARIANT(
        width == sub_width * 2,
        "complex type has two elements of equal bit width");

      return complex_exprt{
        bv_get_rec(complex_real_exprt{expr}, bv, 0 * sub_width),
        bv_get_rec(complex_imag_exprt{expr}, bv, 1 * sub_width),
        to_complex_type(type)};
    }
  }

  const std::size_t width = boolbv_width(type);
  PRECONDITION(bv.size() >= offset + width);

  std::string value;
  value.reserve(width);

  for(std::size_t bit_nr=offset; bit_nr<offset+width; bit_nr++)
  {
    char ch = '0';
    // clang-format off
    switch(prop.l_get(bv[bit_nr]).get_value())
    {
    case tvt::tv_enumt::TV_FALSE: ch = '0'; break;
    case tvt::tv_enumt::TV_TRUE: ch = '1'; break;
    case tvt::tv_enumt::TV_UNKNOWN: ch = '0'; break;
    }
    // clang-format on

    value += ch;
  }

  // The above collects bits starting with the least significant bit,
  // but we need the most significant bit first.
  std::reverse(value.begin(), value.end());

  switch(bvtype)
  {
  case bvtypet::IS_UNKNOWN:
    PRECONDITION(type.id() == ID_string || type.id() == ID_empty);
    if(type.id()==ID_string)
    {
      mp_integer int_value=binary2integer(value, false);
      irep_idt s;
      if(int_value>=string_numbering.size())
        s=irep_idt();
      else
        s = string_numbering[numeric_cast_v<std::size_t>(int_value)];

      return constant_exprt(s, type);
    }
    else if(type.id() == ID_empty)
    {
      return constant_exprt{irep_idt(), type};
    }
    break;

  case bvtypet::IS_RANGE:
  {
    mp_integer int_value = binary2integer(value, false);
    mp_integer from = string2integer(type.get_string(ID_from));

    return constant_exprt(integer2string(int_value + from), type);
    break;
  }

  case bvtypet::IS_C_BIT_FIELD:
  case bvtypet::IS_VERILOG_UNSIGNED:
  case bvtypet::IS_VERILOG_SIGNED:
  case bvtypet::IS_C_BOOL:
  case bvtypet::IS_FIXED:
  case bvtypet::IS_FLOAT:
  case bvtypet::IS_UNSIGNED:
  case bvtypet::IS_SIGNED:
  case bvtypet::IS_BV:
  case bvtypet::IS_C_ENUM:
  {
    const irep_idt bvrep = make_bvrep(
      width, [&value](size_t i) { return value[value.size() - i - 1] == '1'; });
    return constant_exprt(bvrep, type);
  }
  }

  UNREACHABLE;
}

exprt boolbvt::bv_get(const bvt &bv, const typet &type) const
{
  nil_exprt skeleton;
  skeleton.type() = type;
  return bv_get_rec(skeleton, bv, 0);
}

exprt boolbvt::bv_get_cache(const exprt &expr) const
{
  if(expr.is_boolean())
    return get(expr);

  // look up literals in cache
  bv_cachet::const_iterator it=bv_cache.find(expr);
  CHECK_RETURN(it != bv_cache.end());

  return bv_get(it->second, expr.type());
}

exprt boolbvt::bv_get_unbounded_array(const exprt &expr) const
{
  // first, try to get size

  const typet &type=expr.type();
  const exprt &size_expr=to_array_type(type).size();
  exprt size=simplify_expr(get(size_expr), ns);

  // get the numeric value, unless it's infinity
  const auto size_opt = numeric_cast<mp_integer>(size);

  // search array indices, and only use those applicable to a particular model
  // (array theory may have seen other indices, which might only be live under a
  // different model)

  typedef std::map<mp_integer, exprt> valuest;
  valuest values;

  const auto opt_num = arrays.get_number(expr);
  if(opt_num.has_value())
  {
    // get root
    const auto number = arrays.find_number(*opt_num);

    CHECK_RETURN(number < index_map.size());
    index_mapt::const_iterator it=index_map.find(number);
    CHECK_RETURN(it != index_map.end());
    const index_sett &index_set=it->second;

    for(index_sett::const_iterator it1=
        index_set.begin();
        it1!=index_set.end();
        it1++)
    {
      index_exprt index(expr, *it1);

      exprt value=bv_get_cache(index);
      exprt index_value=bv_get_cache(*it1);

      if(!index_value.is_nil())
      {
        const auto index_mpint = numeric_cast<mp_integer>(index_value);

        if(
          index_mpint.has_value() && *index_mpint >= 0 &&
          (!size_opt.has_value() || *index_mpint < *size_opt))
        {
          if(value.is_nil())
            values[*index_mpint] =
              exprt(ID_unknown, to_array_type(type).subtype());
          else
            values[*index_mpint] = value;
        }
      }
    }
  }

  exprt result;

  if(!size_opt.has_value() || values.size() != *size_opt)
  {
    result = array_list_exprt({}, to_array_type(type));

    result.operands().reserve(values.size()*2);

    for(valuest::const_iterator it=values.begin();
        it!=values.end();
        it++)
    {
      exprt index=from_integer(it->first, size.type());
      result.add_to_operands(std::move(index), exprt{it->second});
    }
  }
  else
  {
    // set the size
    result=exprt(ID_array, type);

    // allocate operands
    std::size_t size_int = numeric_cast_v<std::size_t>(*size_opt);
    result.operands().resize(size_int, exprt{ID_unknown});

    // search uninterpreted functions

    for(valuest::iterator it=values.begin();
        it!=values.end();
        it++)
    {
      result.operands()[numeric_cast_v<std::size_t>(it->first)].swap(
        it->second);
    }
  }

  return result;
}

mp_integer boolbvt::get_value(
  const bvt &bv,
  std::size_t offset,
  std::size_t width)
{
  PRECONDITION(offset + width <= bv.size());

  mp_integer value=0;
  mp_integer weight=1;

  for(std::size_t bit_nr=offset; bit_nr<offset+width; bit_nr++)
  {
    switch(prop.l_get(bv[bit_nr]).get_value())
    {
     case tvt::tv_enumt::TV_FALSE:   break;
     case tvt::tv_enumt::TV_TRUE:    value+=weight; break;
     case tvt::tv_enumt::TV_UNKNOWN: break;
     default:
       UNREACHABLE;
    }

    weight*=2;
  }

  return value;
}
