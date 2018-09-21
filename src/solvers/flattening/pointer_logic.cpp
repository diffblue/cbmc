/*******************************************************************\

Module: Pointer Logic

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Logic

#include "pointer_logic.h"

#include <cassert>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/invariant.h>
#include <util/pointer_offset_size.h>
#include <util/prefix.h>
#include <util/std_expr.h>

bool pointer_logict::is_dynamic_object(const exprt &expr) const
{
  if(expr.type().get_bool(ID_C_dynamic))
    return true;

  if(expr.id()==ID_symbol)
    if(has_prefix(id2string(to_symbol_expr(expr).get_identifier()),
                  "symex_dynamic::"))
      return true;

  return false;
}

void pointer_logict::get_dynamic_objects(std::vector<std::size_t> &o) const
{
  o.clear();
  std::size_t nr=0;

  for(pointer_logict::objectst::const_iterator
      it=objects.begin();
      it!=objects.end();
      it++, nr++)
    if(is_dynamic_object(*it))
      o.push_back(nr);
}

std::size_t pointer_logict::add_object(const exprt &expr)
{
  // remove any index/member

  if(expr.id()==ID_index)
  {
    assert(expr.operands().size()==2);
    return add_object(expr.op0());
  }
  else if(expr.id()==ID_member)
  {
    assert(expr.operands().size()==1);
    return add_object(expr.op0());
  }

  return objects.number(expr);
}

exprt pointer_logict::pointer_expr(
  std::size_t object,
  const pointer_typet &type) const
{
  pointert pointer(object, 0);
  return pointer_expr(pointer, type);
}

exprt pointer_logict::pointer_expr(
  const pointert &pointer,
  const pointer_typet &type) const
{
  if(pointer.object==null_object) // NULL?
  {
    if(pointer.offset==0)
    {
      null_pointer_exprt result(type);
      return result;
    }
    else
    {
      null_pointer_exprt null(type);
      return plus_exprt(null,
        from_integer(pointer.offset, pointer_diff_type()));
    }
  }
  else if(pointer.object==invalid_object) // INVALID?
  {
    return constant_exprt("INVALID", type);
  }

  if(pointer.object>=objects.size())
  {
    return constant_exprt("INVALID-" + std::to_string(pointer.object), type);
  }

  const exprt &object_expr=objects[pointer.object];

  exprt deep_object=object_rec(pointer.offset, type, object_expr);

  return address_of_exprt(deep_object, type);
}

exprt pointer_logict::object_rec(
  const mp_integer &offset,
  const typet &pointer_type,
  const exprt &src) const
{
  if(src.type().id()==ID_array)
  {
    mp_integer size=
      pointer_offset_size(src.type().subtype(), ns);

    if(size<=0)
      return src;

    mp_integer index=offset/size;
    mp_integer rest=offset%size;
    if(rest<0)
      rest=-rest;

    index_exprt tmp(src.type().subtype());
    tmp.index()=from_integer(index, typet(ID_integer));
    tmp.array()=src;

    return object_rec(rest, pointer_type, tmp);
  }
  else if(src.type().id()==ID_struct)
  {
    const struct_typet::componentst &components=
      to_struct_type(src.type()).components();

    if(offset<0)
      return src;

    mp_integer current_offset=0;

    for(const auto &c : components)
    {
      assert(offset>=current_offset);

      const typet &subtype=c.type();

      mp_integer sub_size=pointer_offset_size(subtype, ns);
      assert(sub_size>0);
      mp_integer new_offset=current_offset+sub_size;

      if(new_offset>offset)
      {
        // found it
        member_exprt tmp(src, c);

        return object_rec(
          offset-current_offset, pointer_type, tmp);
      }

      assert(new_offset<=offset);
      current_offset=new_offset;
      assert(current_offset<=offset);
    }

    return src;
  }
  else if(src.type().id()==ID_union)
    return src;

  return src;
}

pointer_logict::pointer_logict(const namespacet &_ns):ns(_ns)
{
  // add NULL
  null_object=objects.number(exprt(ID_NULL));
  assert(null_object==0);

  // add INVALID
  invalid_object=objects.number(exprt("INVALID"));
}

pointer_logict::~pointer_logict()
{
}
