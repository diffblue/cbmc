/*******************************************************************\

Module: Pointer Logic

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/i2string.h>
#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/prefix.h>
#include <util/pointer_offset_size.h>

#include "pointer_logic.h"

/*******************************************************************\

Function: pointer_logict::is_dynamic_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool pointer_logict::is_dynamic_object(const exprt &expr) const
{
  if(expr.type().get_bool("#dynamic")) return true;
  
  if(expr.id()==ID_symbol)
    if(has_prefix(id2string(to_symbol_expr(expr).get_identifier()),
                  "symex_dynamic::"))
      return true;

  return false;
}

/*******************************************************************\

Function: pointer_logict::get_dynamic_objects

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void pointer_logict::get_dynamic_objects(std::vector<unsigned> &o) const
{
  o.clear();
  unsigned nr=0;
  
  for(pointer_logict::objectst::const_iterator
      it=objects.begin();
      it!=objects.end();
      it++, nr++)
    if(is_dynamic_object(*it))
      o.push_back(nr);
}

/*******************************************************************\

Function: pointer_logict::add_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned pointer_logict::add_object(const exprt &expr)
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

/*******************************************************************\

Function: pointer_logict::pointer_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt pointer_logict::pointer_expr(
  unsigned object,
  const typet &type) const
{
  pointert pointer(object, 0);
  return pointer_expr(pointer, type);
}

/*******************************************************************\

Function: pointer_logict::pointer_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt pointer_logict::pointer_expr(
  const pointert &pointer,
  const typet &type) const
{
  if(pointer.object==null_object) // NULL?
  {
    if(pointer.offset==0)
    {
      constant_exprt result(type);
      result.set_value(ID_NULL);
      return result;
    }
    else
    {
      constant_exprt null(type);
      null.set_value(ID_NULL);
      return plus_exprt(null,
        from_integer(pointer.offset, integer_typet()));
    }
  }
  else if(pointer.object==invalid_object) // INVALID?
  {
    constant_exprt result(type);
    result.set_value("INVALID");
    return result;
  }
  
  if(pointer.object>=objects.size() || pointer.object<0)
  {
    constant_exprt result(type);
    result.set_value("INVALID-"+i2string(pointer.object));
    return result;
  }

  const exprt &object_expr=objects[pointer.object];

  exprt deep_object=object_rec(pointer.offset, type, object_expr);
  
  exprt result;
  
  if(type.id()==ID_pointer)
    result=exprt(ID_address_of, type);
  else if(type.id()==ID_reference)
    result=exprt("reference_to", type);
  else
    assert(0);

  result.copy_to_operands(deep_object);
  return result;
}

/*******************************************************************\

Function: pointer_logict::object_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt pointer_logict::object_rec(
  const mp_integer &offset,
  const typet &pointer_type,
  const exprt &src) const
{
  if(src.type().id()==ID_array)
  {
    mp_integer size=
      pointer_offset_size(ns, src.type().subtype());

    if(size==0) return src;
    
    mp_integer index=offset/size;
    mp_integer rest=offset%size;
    if(rest<0) rest=-rest;

    index_exprt tmp(src.type().subtype());
    tmp.index()=from_integer(index, typet(ID_integer));
    tmp.array()=src;
    
    return object_rec(rest, pointer_type, tmp);
  }
  else if(src.type().id()==ID_struct)
  {
    const struct_typet::componentst &components=
      to_struct_type(src.type()).components();

    if(offset<0) return src;

    mp_integer current_offset=0;

    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      assert(offset>=current_offset);

      const typet &subtype=it->type();

      mp_integer sub_size=pointer_offset_size(ns, subtype);
      mp_integer new_offset=current_offset+sub_size;

      if(new_offset>offset)
      {
        // found it
        member_exprt tmp(subtype);
        tmp.set_component_name(it->get_name());
        tmp.op0()=src;
        
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

/*******************************************************************\

Function: pointer_logict::pointer_logict

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

pointer_logict::pointer_logict(const namespacet &_ns):ns(_ns)
{
  // add NULL
  null_object=objects.number(exprt(ID_NULL));
  assert(null_object==0);

  // add INVALID
  invalid_object=objects.number(exprt("INVALID"));
}

/*******************************************************************\

Function: pointer_logict::~pointer_logict

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

pointer_logict::~pointer_logict()
{
}
