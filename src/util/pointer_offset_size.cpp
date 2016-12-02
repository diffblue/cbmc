/*******************************************************************\

Module: Pointer Logic

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "expr.h"
#include "arith_tools.h"
#include "std_types.h"
#include "std_expr.h"
#include "expr_util.h"
#include "config.h"
#include "simplify_expr.h"
#include "namespace.h"
#include "symbol.h"
#include "ssa_expr.h"

#include "pointer_offset_size.h"

member_offset_iterator::member_offset_iterator(const struct_typet& _type,
                                               const namespacet& _ns) :
  current({0,0}),
  type(_type),
  ns(_ns),
  bit_field_bits(0)
{
}

member_offset_iterator& member_offset_iterator::operator++()
{
  if(current.second!=-1) // Already failed?
  {
    const auto& comp=type.components()[current.first];
    if(comp.type().id()==ID_c_bit_field)
    {
      // take the extra bytes needed
      std::size_t w=to_c_bit_field_type(comp.type()).get_width();
      for(; w>bit_field_bits; ++current.second, bit_field_bits+=8);
      bit_field_bits-=w;
    }
    else
    {
      const typet &subtype=comp.type();
      mp_integer sub_size=pointer_offset_size(subtype, ns);
      if(sub_size==-1) current.second=-1; // give up
      else current.second+=sub_size;
    }
  }
  ++current.first;
  return *this;
}

/*******************************************************************\

Function: member_offset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer member_offset(
  const struct_typet &type,
  const irep_idt &member,
  const namespacet &ns)
{
  const struct_typet::componentst &components=type.components();
  member_offset_iterator offsets(type,ns);

  for(struct_typet::componentst::const_iterator
      it=components.begin();
      it!=components.end() && offsets->second!=-1;
      ++it, ++offsets)
  {
    if(it->get_name()==member)
      break;
  }

  return offsets->second;
}

/*******************************************************************\

Function: pointer_offset_size

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer pointer_offset_size(
  const typet &type,
  const namespacet &ns)
{
  mp_integer bits=pointer_offset_bits(type, ns);
  if(bits==-1) return -1;
  return bits/8+(((bits%8)==0)?0:1);
}

/*******************************************************************\

Function: pointer_offset_bits

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer pointer_offset_bits(
  const typet &type,
  const namespacet &ns)
{
  if(type.id()==ID_array)
  {
    mp_integer sub=pointer_offset_bits(type.subtype(), ns);

    // get size
    const exprt &size=to_array_type(type).size();

    // constant?
    mp_integer i;

    if(to_integer(size, i))
      return -1; // we cannot distinguish the elements

    return sub*i;
  }
  else if(type.id()==ID_vector)
  {
    mp_integer sub=pointer_offset_bits(type.subtype(), ns);

    // get size
    const exprt &size=to_vector_type(type).size();

    // constant?
    mp_integer i;

    if(to_integer(size, i))
      return -1; // we cannot distinguish the elements

    return sub*i;
  }
  else if(type.id()==ID_complex)
  {
    mp_integer sub=pointer_offset_bits(type.subtype(), ns);
    return sub*2;
  }
  else if(type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(type);
    const struct_typet::componentst &components=
      struct_type.components();

    mp_integer result=0;

    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      const typet &subtype=it->type();
      mp_integer sub_size=pointer_offset_bits(subtype, ns);
      if(sub_size==-1) return -1;
      result+=sub_size;
    }

    return result;
  }
  else if(type.id()==ID_union)
  {
    const union_typet &union_type=to_union_type(type);
    const union_typet::componentst &components=
      union_type.components();

    mp_integer result=0;

    // compute max

    for(union_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      const typet &subtype=it->type();
      mp_integer sub_size=pointer_offset_bits(subtype, ns);
      if(sub_size>result) result=sub_size;
    }

    return result;
  }
  else if(type.id()==ID_signedbv ||
          type.id()==ID_unsignedbv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_floatbv ||
          type.id()==ID_bv ||
          type.id()==ID_c_bool)
  {
    return to_bitvector_type(type).get_width();
  }
  else if(type.id()==ID_c_bit_field)
  {
    return to_c_bit_field_type(type).get_width();
  }
  else if(type.id()==ID_c_enum)
  {
    return to_bitvector_type(type.subtype()).get_width();
  }
  else if(type.id()==ID_c_enum_tag)
  {
    return pointer_offset_bits(ns.follow_tag(to_c_enum_tag_type(type)), ns);
  }
  else if(type.id()==ID_bool)
  {
    return 1;
  }
  else if(type.id()==ID_pointer)
  {
    return config.ansi_c.pointer_width;
  }
  else if(type.id()==ID_symbol)
  {
    return pointer_offset_bits(ns.follow(type), ns);
  }
  else if(type.id()==ID_code)
  {
    return 0;
  }
  else if(type.id()==ID_string)
  {
    return 32;
  }
  else
    return mp_integer(-1);
}

/*******************************************************************\

Function: member_offset_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt member_offset_expr(
  const member_exprt &member_expr,
  const namespacet &ns)
{
  // need to distinguish structs and unions
  const typet &type=ns.follow(member_expr.struct_op().type());
  if(type.id()==ID_struct)
    return member_offset_expr(
      to_struct_type(type), member_expr.get_component_name(), ns);
  else if(type.id()==ID_union)
    return gen_zero(signedbv_typet(config.ansi_c.pointer_width));
  else
    return nil_exprt();
}

/*******************************************************************\

Function: member_offset_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt member_offset_expr(
  const struct_typet &type,
  const irep_idt &member,
  const namespacet &ns)
{
  const struct_typet::componentst &components=type.components();

  exprt result=gen_zero(signedbv_typet(config.ansi_c.pointer_width));
  std::size_t bit_field_bits=0;

  for(struct_typet::componentst::const_iterator
      it=components.begin();
      it!=components.end();
      it++)
  {
    if(it->get_name()==member) break;

    if(it->type().id()==ID_c_bit_field)
    {
      std::size_t w=to_c_bit_field_type(it->type()).get_width();
      std::size_t bytes;
      for(bytes=0; w>bit_field_bits; ++bytes, bit_field_bits+=8);
      bit_field_bits-=w;
      result=plus_exprt(result, from_integer(bytes, result.type()));
    }
    else
    {
      const typet &subtype=it->type();
      exprt sub_size=size_of_expr(subtype, ns);
      if(sub_size.is_nil()) return nil_exprt(); // give up
      result=plus_exprt(result, sub_size);
    }
  }

  simplify(result, ns);

  return result;
}

/*******************************************************************\

Function: size_of_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt size_of_expr(
  const typet &type,
  const namespacet &ns)
{
  if(type.id()==ID_array)
  {
    exprt sub=size_of_expr(type.subtype(), ns);
    if(sub.is_nil()) return nil_exprt();

    // get size
    exprt size=to_array_type(type).size();

    if(size.is_nil()) return nil_exprt();

    if(size.type()!=sub.type())
      size.make_typecast(sub.type());

    exprt result=mult_exprt(size, sub);

    simplify(result, ns);

    return result;
  }
  else if(type.id()==ID_vector)
  {
    exprt sub=size_of_expr(type.subtype(), ns);
    if(sub.is_nil()) return nil_exprt();

    // get size
    exprt size=to_vector_type(type).size();

    if(size.is_nil()) return nil_exprt();

    if(size.type()!=sub.type())
      size.make_typecast(sub.type());

    exprt result=mult_exprt(size, sub);
    simplify(result, ns);

    return result;
  }
  else if(type.id()==ID_complex)
  {
    exprt sub=size_of_expr(type.subtype(), ns);
    if(sub.is_nil()) return nil_exprt();

    const exprt size=from_integer(2, sub.type());

    exprt result=mult_exprt(size, sub);
    simplify(result, ns);

    return result;
  }
  else if(type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(type);
    const struct_typet::componentst &components=
      struct_type.components();

    exprt result=gen_zero(signedbv_typet(config.ansi_c.pointer_width));
    std::size_t bit_field_bits=0;

    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      if(it->type().id()==ID_c_bit_field)
      {
        std::size_t w=to_c_bit_field_type(it->type()).get_width();
        std::size_t bytes;
        for(bytes=0; w>bit_field_bits; ++bytes, bit_field_bits+=8);
        bit_field_bits-=w;
        result=plus_exprt(result, from_integer(bytes, result.type()));
      }
      else
      {
        const typet &subtype=it->type();
        exprt sub_size=size_of_expr(subtype, ns);
        if(sub_size.is_nil()) return nil_exprt();

        result=plus_exprt(result, sub_size);
      }
    }

    simplify(result, ns);

    return result;
  }
  else if(type.id()==ID_union)
  {
    const union_typet &union_type=to_union_type(type);
    const union_typet::componentst &components=
      union_type.components();

    mp_integer result=0;

    // compute max

    for(union_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      const typet &subtype=it->type();
      mp_integer sub_size;

      if(subtype.id()==ID_c_bit_field)
      {
        std::size_t bits=to_c_bit_field_type(subtype).get_width();
        sub_size=bits/8;
        if((bits%8)!=0) ++sub_size;
      }
      else
        sub_size=pointer_offset_size(subtype, ns);

      if(sub_size>result) result=sub_size;
    }

    return from_integer(result, signedbv_typet(config.ansi_c.pointer_width));
  }
  else if(type.id()==ID_signedbv ||
          type.id()==ID_unsignedbv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_floatbv ||
          type.id()==ID_bv ||
          type.id()==ID_c_bool)
  {
    std::size_t width=to_bitvector_type(type).get_width();
    std::size_t bytes=width/8;
    if(bytes*8!=width) bytes++;
    return from_integer(bytes, signedbv_typet(config.ansi_c.pointer_width));
  }
  else if(type.id()==ID_c_enum)
  {
    std::size_t width=to_bitvector_type(type.subtype()).get_width();
    std::size_t bytes=width/8;
    if(bytes*8!=width) bytes++;
    return from_integer(bytes, signedbv_typet(config.ansi_c.pointer_width));
  }
  else if(type.id()==ID_c_enum_tag)
  {
    return size_of_expr(ns.follow_tag(to_c_enum_tag_type(type)), ns);
  }
  else if(type.id()==ID_bool)
  {
    return gen_one(signedbv_typet(config.ansi_c.pointer_width));
  }
  else if(type.id()==ID_pointer)
  {
    std::size_t width=config.ansi_c.pointer_width;
    std::size_t bytes=width/8;
    if(bytes*8!=width) bytes++;
    return from_integer(bytes, signedbv_typet(config.ansi_c.pointer_width));
  }
  else if(type.id()==ID_symbol)
  {
    return size_of_expr(ns.follow(type), ns);
  }
  else if(type.id()==ID_code)
  {
    return gen_zero(signedbv_typet(config.ansi_c.pointer_width));
  }
  else if(type.id()==ID_string)
  {
    return from_integer(
      32/8, signedbv_typet(config.ansi_c.pointer_width));
  }
  else
    return nil_exprt();
}

/*******************************************************************\

Function: compute_pointer_offset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer compute_pointer_offset(
  const exprt &expr,
  const namespacet &ns)
{
  if(expr.id()==ID_symbol)
  {
    if(is_ssa_expr(expr))
      return compute_pointer_offset(
        to_ssa_expr(expr).get_original_expr(), ns);
    else
      return 0;
  }
  else if(expr.id()==ID_index)
  {
    assert(expr.operands().size()==2);

    const typet &array_type=ns.follow(expr.op0().type());
    assert(array_type.id()==ID_array);

    mp_integer o=compute_pointer_offset(expr.op0(), ns);

    if(o!=-1)
    {
      mp_integer sub_size=
        pointer_offset_size(array_type.subtype(), ns);

      mp_integer i;

      if(sub_size!=0 && !to_integer(expr.op1(), i))
        return o+i*sub_size;
    }

    // don't know
  }
  else if(expr.id()==ID_member)
  {
    assert(expr.operands().size()==1);
    const typet &type=ns.follow(expr.op0().type());

    assert(type.id()==ID_struct ||
           type.id()==ID_union);

    mp_integer o=compute_pointer_offset(expr.op0(), ns);

    if(o!=-1)
    {
      if(type.id()==ID_union)
        return o;

      return o+member_offset(
        to_struct_type(type), expr.get(ID_component_name), ns);
    }
  }
  else if(expr.id()==ID_string_constant)
    return 0;

  return -1; // don't know
}

/*******************************************************************\

Function: build_sizeof_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt build_sizeof_expr(
  const constant_exprt &expr,
  const namespacet &ns)
{
  const typet &type=
    static_cast<const typet &>(expr.find(ID_C_c_sizeof_type));

  mp_integer type_size=-1, val=-1;

  if(type.is_not_nil()) type_size=pointer_offset_size(type, ns);

  if(type_size<0 ||
     to_integer(expr, val) ||
     val<type_size ||
     (type_size==0 && val>0))
    return nil_exprt();

  assert(address_bits(val+1)<=config.ansi_c.pointer_width);
  const unsignedbv_typet t(config.ansi_c.pointer_width);

  mp_integer remainder=0;
  if(type_size!=0)
  {
    remainder=val%type_size;
    val-=remainder;
    val/=type_size;
  }

  exprt result(ID_sizeof, t);
  result.set(ID_type_arg, type);

  if(val>1)
    result=mult_exprt(result, from_integer(val, t));
  if(remainder>0)
    result=plus_exprt(result, from_integer(remainder, t));

  if(result.type()!=expr.type())
    result.make_typecast(expr.type());

  return result;
}

bool get_subexpression_at_offset(
  exprt& result,
  mp_integer offset,
  const typet& target_type_raw,
  const namespacet& ns)
{
  const typet& source_type=ns.follow(result.type());
  const typet& target_type=ns.follow(target_type_raw);

  if(offset==0 && source_type==target_type)
    return true;

  if(source_type.id()==ID_struct)
  {
    const auto& st=to_struct_type(source_type);
    const struct_typet::componentst &components=st.components();
    member_offset_iterator offsets(st,ns);
    while(offsets->first<components.size() && offsets->second!=-1 && offsets->second<=offset)
    {
      auto nextit=offsets;
      ++nextit;
      if((offsets->first+1)==components.size() || offset<nextit->second)
      {
	// This field might be, or might contain, the answer.
	result=member_exprt(result,
			    components[offsets->first].get_name(),
			    components[offsets->first].type());
	return get_subexpression_at_offset(result, offset - offsets->second, target_type, ns);
      }
      ++offsets;
    }
    return false;
  }
  else if(source_type.id()==ID_array)
  {
    // A cell of the array might be, or contain, the subexpression we're looking for.
    const auto& at=to_array_type(source_type);
    mp_integer elem_size=pointer_offset_size(at.subtype(),ns);
    if(elem_size==-1)
      return false;
    mp_integer cellidx=offset / elem_size;
    if(cellidx < 0 || !cellidx.is_long())
      return false;
    offset=offset % elem_size;
    result=index_exprt(result,from_integer(cellidx,unsignedbv_typet(64)));
    return get_subexpression_at_offset(result,offset,target_type,ns);
  }
  else
    return false;

}

bool get_subexpression_at_offset(
  exprt& result,
  const exprt& offset,
  const typet& target_type,
  const namespacet& ns)
{
  mp_integer offset_const;
  if(to_integer(offset,offset_const))
    return false;
  return get_subexpression_at_offset(result,offset_const,target_type,ns);
}
