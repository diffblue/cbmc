/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <cassert>

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/threeval.h>
#include <util/std_types.h>
#include <util/simplify_expr.h>

#include "boolbv_type.h"

exprt boolbvt::get(const exprt &expr) const
{
  if(expr.id()==ID_symbol ||
     expr.id()==ID_nondet_symbol)
  {
    const irep_idt &identifier=expr.get(ID_identifier);

    boolbv_mapt::mappingt::const_iterator it=
      map.mapping.find(identifier);

    if(it!=map.mapping.end())
    {
      const boolbv_mapt::map_entryt &map_entry=it->second;

      if(is_unbounded_array(map_entry.type))
        return bv_get_unbounded_array(expr);

      std::vector<bool> unknown;
      bvt bv;
      std::size_t width=map_entry.width;

      bv.resize(width);
      unknown.resize(width);

      for(std::size_t bit_nr=0; bit_nr<width; bit_nr++)
      {
        assert(bit_nr<map_entry.literal_map.size());

        if(map_entry.literal_map[bit_nr].is_set)
        {
          unknown[bit_nr]=false;
          bv[bit_nr]=map_entry.literal_map[bit_nr].l;
        }
        else
        {
          unknown[bit_nr]=true;
          bv[bit_nr].clear();
        }
      }

      return bv_get_rec(bv, unknown, 0, map_entry.type);
    }
  }

  return SUB::get(expr);
}

exprt boolbvt::bv_get_rec(
  const bvt &bv,
  const std::vector<bool> &unknown,
  std::size_t offset,
  const typet &type) const
{
  std::size_t width=boolbv_width(type);

  assert(bv.size()==unknown.size());
  assert(bv.size()>=offset+width);

  if(type.id()==ID_bool)
  {
    if(!unknown[offset])
    {
      switch(prop.l_get(bv[offset]).get_value())
      {
      case tvt::tv_enumt::TV_FALSE: return false_exprt();
      case tvt::tv_enumt::TV_TRUE:  return true_exprt();
      default: return false_exprt(); // default
      }
    }

    return nil_exprt();
  }

  bvtypet bvtype=get_bvtype(type);

  if(bvtype==bvtypet::IS_UNKNOWN)
  {
    if(type.id()==ID_array)
    {
      const typet &subtype=type.subtype();
      std::size_t sub_width=boolbv_width(subtype);

      if(sub_width!=0)
      {
        exprt::operandst op;
        op.reserve(width/sub_width);

        for(std::size_t new_offset=0;
            new_offset<width;
            new_offset+=sub_width)
        {
          op.push_back(
            bv_get_rec(bv, unknown, offset+new_offset, subtype));
        }

        exprt dest=exprt(ID_array, type);
        dest.operands().swap(op);
        return dest;
      }
    }
    else if(type.id()==ID_struct_tag)
    {
      return
        bv_get_rec(
          bv, unknown, offset, ns.follow_tag(to_struct_tag_type(type)));
    }
    else if(type.id()==ID_union_tag)
    {
      return
        bv_get_rec(
          bv, unknown, offset, ns.follow_tag(to_union_tag_type(type)));
    }
    else if(type.id()==ID_struct)
    {
      const struct_typet &struct_type=to_struct_type(type);
      const struct_typet::componentst &components=struct_type.components();
      std::size_t new_offset=0;
      exprt::operandst op;
      op.reserve(components.size());

      for(const auto &c : components)
      {
        const typet &subtype = c.type();
        op.push_back(nil_exprt());

        std::size_t sub_width=boolbv_width(subtype);

        if(sub_width!=0)
        {
          op.back()=bv_get_rec(bv, unknown, offset+new_offset, subtype);
          new_offset+=sub_width;
        }
      }

      return struct_exprt(std::move(op), type);
    }
    else if(type.id()==ID_union)
    {
      const union_typet &union_type=to_union_type(type);
      const union_typet::componentst &components=union_type.components();

      assert(!components.empty());

      // Any idea that's better than just returning the first component?
      std::size_t component_nr=0;

      const typet &subtype = components[component_nr].type();

      return union_exprt(
        components[component_nr].get_name(),
        bv_get_rec(bv, unknown, offset, subtype),
        union_type);
    }
    else if(type.id()==ID_vector)
    {
      const typet &subtype = type.subtype();
      std::size_t sub_width=boolbv_width(subtype);

      if(sub_width!=0 && width%sub_width==0)
      {
        std::size_t size=width/sub_width;
        vector_exprt value(to_vector_type(type));
        value.reserve_operands(size);

        for(std::size_t i=0; i<size; i++)
          value.operands().push_back(
            bv_get_rec(bv, unknown, i*sub_width, subtype));

        return std::move(value);
      }
    }
    else if(type.id()==ID_complex)
    {
      const typet &subtype = type.subtype();
      std::size_t sub_width=boolbv_width(subtype);

      if(sub_width!=0 && width==sub_width*2)
      {
        const complex_exprt value(
          bv_get_rec(bv, unknown, 0 * sub_width, subtype),
          bv_get_rec(bv, unknown, 1 * sub_width, subtype),
          to_complex_type(type));

        return value;
      }
    }
  }

  // most significant bit first
  std::string value;

  for(std::size_t bit_nr=offset; bit_nr<offset+width; bit_nr++)
  {
    char ch = '0';
    if(!unknown[bit_nr])
    {
      switch(prop.l_get(bv[bit_nr]).get_value())
      {
       case tvt::tv_enumt::TV_FALSE: ch='0'; break;
       case tvt::tv_enumt::TV_TRUE:  ch='1'; break;
       case tvt::tv_enumt::TV_UNKNOWN: ch='0'; break;
       default: UNREACHABLE;
      }
    }

    value=ch+value;
  }

  switch(bvtype)
  {
  case bvtypet::IS_UNKNOWN:
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
    break;

  case bvtypet::IS_RANGE:
    {
      mp_integer int_value=binary2integer(value, false);
      mp_integer from=string2integer(type.get_string(ID_from));

      return constant_exprt(integer2string(int_value + from), type);
    }
    break;

  default:
  case bvtypet::IS_C_ENUM:
  {
    const irep_idt bvrep = make_bvrep(
      width, [&value](size_t i) { return value[value.size() - i - 1] == '1'; });
    return constant_exprt(bvrep, type);
  }
  }

  return nil_exprt();
}

exprt boolbvt::bv_get(const bvt &bv, const typet &type) const
{
  std::vector<bool> unknown;
  unknown.resize(bv.size(), false);
  return bv_get_rec(bv, unknown, 0, type);
}

exprt boolbvt::bv_get_cache(const exprt &expr) const
{
  if(expr.type().id()==ID_bool) // boolean?
    return get(expr);

  // look up literals in cache
  bv_cachet::const_iterator it=bv_cache.find(expr);
  if(it==bv_cache.end())
    return nil_exprt();

  return bv_get(it->second, expr.type());
}

exprt boolbvt::bv_get_unbounded_array(const exprt &expr) const
{
  // first, try to get size

  const typet &type=expr.type();
  const exprt &size_expr=to_array_type(type).size();
  exprt size=simplify_expr(get(size_expr), ns);

  // no size, give up
  if(size.is_nil())
    return nil_exprt();

  // get the numeric value, unless it's infinity
  mp_integer size_mpint;

  if(size.id()!=ID_infinity)
  {
    if(to_integer(size, size_mpint))
      return nil_exprt();

    // simple sanity check
    if(size_mpint<0)
      return nil_exprt();
  }
  else
    size_mpint=0;

  // search array indices

  typedef std::map<mp_integer, exprt> valuest;
  valuest values;

  {
    const auto opt_num = arrays.get_number(expr);
    if(!opt_num)
    {
      return nil_exprt();
    }

    // get root
    const auto number = arrays.find_number(*opt_num);

    assert(number<index_map.size());
    index_mapt::const_iterator it=index_map.find(number);
    assert(it!=index_map.end());
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
        mp_integer index_mpint;

        if(!to_integer(index_value, index_mpint))
        {
          if(value.is_nil())
            values[index_mpint]=exprt(ID_unknown, type.subtype());
          else
            values[index_mpint]=value;
        }
      }
    }
  }

  exprt result;

  if(size_mpint>100 || size.id()==ID_infinity)
  {
    result = array_list_exprt(to_array_type(type));
    result.type().set(ID_size, integer2string(size_mpint));

    result.operands().reserve(values.size()*2);

    for(valuest::const_iterator it=values.begin();
        it!=values.end();
        it++)
    {
      exprt index=from_integer(it->first, size.type());
      result.copy_to_operands(index, it->second);
    }
  }
  else
  {
    // set the size
    result=exprt(ID_array, type);
    result.type().set(ID_size, size);

    std::size_t size_int = numeric_cast_v<std::size_t>(size_mpint);

    // allocate operands
    result.operands().resize(size_int);

    for(std::size_t i=0; i<size_int; i++)
      result.operands()[i]=exprt(ID_unknown);

    // search uninterpreted functions

    for(valuest::iterator it=values.begin();
        it!=values.end();
        it++)
      if(it->first>=0 && it->first<size_mpint)
        result.operands()[numeric_cast_v<std::size_t>(it->first)].swap(
          it->second);
  }

  return result;
}

mp_integer boolbvt::get_value(
  const bvt &bv,
  std::size_t offset,
  std::size_t width)
{
  mp_integer value=0;
  mp_integer weight=1;

  for(std::size_t bit_nr=offset; bit_nr<offset+width; bit_nr++)
  {
    assert(bit_nr<bv.size());
    switch(prop.l_get(bv[bit_nr]).get_value())
    {
     case tvt::tv_enumt::TV_FALSE:   break;
     case tvt::tv_enumt::TV_TRUE:    value+=weight; break;
     case tvt::tv_enumt::TV_UNKNOWN: break;
     default: assert(false);
    }

    weight*=2;
  }

  return value;
}
