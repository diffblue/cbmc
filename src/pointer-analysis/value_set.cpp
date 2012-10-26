/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <context.h>
#include <simplify_expr.h>
#include <expr_util.h>
#include <base_type.h>
#include <std_expr.h>
#include <i2string.h>
#include <prefix.h>
#include <std_code.h>
#include <arith_tools.h>
#include <pointer_offset_size.h>
#include <cprover_prefix.h>

#include <langapi/language_util.h>
#include <ansi-c/c_types.h>

#include "value_set.h"
#include "add_failed_symbols.h"

const value_sett::object_map_dt value_sett::object_map_dt::empty;
object_numberingt value_sett::object_numbering;
   
/*******************************************************************\

Function: value_sett::field_sensitive

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_sett::field_sensitive(
  const irep_idt &id,
  const typet &type)
{
  // we always track fields on these
  if(has_prefix(id2string(id), "value_set::dynamic_object") ||
     id=="value_set::return_value" ||
     id=="value_set::memory")
    return true;

  // otherwise it has to be a struct
  return type.id()==ID_struct;
}

/*******************************************************************\

Function: value_sett::insert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

value_sett::entryt &value_sett::get_entry(
  const entryt &e,
  const typet &type)
{
  irep_idt index;

  if(field_sensitive(e.identifier, type))
    index=id2string(e.identifier)+e.suffix;
  else
    index=e.identifier;

  std::pair<valuest::iterator, bool> r=
    values.insert(std::pair<idt, entryt>(index, e));

  return r.first->second;
}

/*******************************************************************\

Function: value_sett::insert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_sett::insert(
  object_mapt &dest,
  unsigned n,
  const objectt &object) const
{
  object_map_dt::const_iterator entry=dest.read().find(n);

  if(entry==dest.read().end())
  {
    // new
    dest.write()[n]=object;
    return true;
  }
  else if(!entry->second.offset_is_set)
    return false; // no change
  else if(object.offset_is_set &&
          entry->second.offset==object.offset)
    return false; // no change
  else
  {
    dest.write()[n].offset_is_set=false;
    return true;
  }
}

/*******************************************************************\

Function: value_sett::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::output(
  const namespacet &ns,
  std::ostream &out) const
{
  for(valuest::const_iterator
      v_it=values.begin();
      v_it!=values.end();
      v_it++)
  {
    irep_idt identifier, display_name;
    
    const entryt &e=v_it->second;
  
    if(has_prefix(id2string(e.identifier), "value_set::dynamic_object"))
    {
      display_name=id2string(e.identifier)+e.suffix;
      identifier="";
    }
    else if(e.identifier=="value_set::return_value")
    {
      display_name="RETURN_VALUE"+e.suffix;
      identifier="";
    }
    else
    {
      #if 0
      const symbolt &symbol=ns.lookup(e.identifier);
      display_name=symbol.display_name()+e.suffix;
      identifier=symbol.name;
      #else
      identifier=id2string(e.identifier);
      display_name=id2string(identifier)+e.suffix;
      #endif
    }
    
    out << display_name;

    out << " = { ";

    const object_map_dt &object_map=e.object_map.read();
    
    unsigned width=0;
    
    for(object_map_dt::const_iterator
        o_it=object_map.begin();
        o_it!=object_map.end();
        o_it++)
    {
      const exprt &o=object_numbering[o_it->first];
    
      std::string result;

      if(o.id()==ID_invalid || o.id()==ID_unknown)
        result=from_expr(ns, identifier, o);
      else
      {
        result="<"+from_expr(ns, identifier, o)+", ";
      
        if(o_it->second.offset_is_set)
          result+=integer2string(o_it->second.offset)+"";
        else
          result+="*";

        if(o.type().is_nil())
          result+=", ?";
        else
          result+=", "+from_type(ns, identifier, o.type());
      
        result+=">";
      }

      out << result;

      width+=result.size();
    
      object_map_dt::const_iterator next(o_it);
      next++;

      if(next!=object_map.end())
      {
        out << ", ";
        if(width>=40) out << "\n      ";
      }
    }

    out << " } " << std::endl;
  }
}

/*******************************************************************\

Function: value_sett::to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt value_sett::to_expr(object_map_dt::const_iterator it) const
{
  const exprt &object=object_numbering[it->first];
  
  if(object.id()==ID_invalid ||
     object.id()==ID_unknown)
    return object;

  object_descriptor_exprt od;

  od.object()=object;
  
  if(it->second.offset_is_set)
    od.offset()=from_integer(it->second.offset, index_type());

  od.type()=od.object().type();

  return od;
}

/*******************************************************************\

Function: value_sett::make_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_sett::make_union(const value_sett::valuest &new_values)
{
  bool result=false;
  
  valuest::iterator v_it=values.begin();

  for(valuest::const_iterator
      it=new_values.begin();
      it!=new_values.end();
      ) // no it++
  {
    if(v_it==values.end() || it->first<v_it->first)
    {
      values.insert(v_it, *it);
      result=true;
      it++;
      continue;
    }
    else if(v_it->first<it->first)
    {
      v_it++;
      continue;
    }
    
    assert(v_it->first==it->first);
      
    entryt &e=v_it->second;
    const entryt &new_e=it->second;
    
    if(make_union(e.object_map, new_e.object_map))
      result=true;

    v_it++;
    it++;
  }
  
  return result;
}

/*******************************************************************\

Function: value_sett::make_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_sett::make_union(object_mapt &dest, const object_mapt &src) const
{
  bool result=false;
  
  for(object_map_dt::const_iterator it=src.read().begin();
      it!=src.read().end();
      it++)
  {
    if(insert(dest, it))
      result=true;
  }
  
  return result;
}

/*******************************************************************\

Function: value_sett::get_value_set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::get_value_set(
  const exprt &expr,
  value_setst::valuest &dest,
  const namespacet &ns) const
{
  object_mapt object_map;
  get_value_set(expr, object_map, ns);
  
  for(object_map_dt::const_iterator
      it=object_map.read().begin();
      it!=object_map.read().end();
      it++)
    dest.push_back(to_expr(it));

  #if 0
  for(value_setst::valuest::const_iterator it=dest.begin(); it!=dest.end(); it++)
    std::cout << "GET_VALUE_SET: " << from_expr(ns, "", *it) << std::endl;
  #endif
}

/*******************************************************************\

Function: value_sett::get_value_set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::get_value_set(
  const exprt &expr,
  object_mapt &dest,
  const namespacet &ns) const
{
  exprt tmp(expr);
  simplify(tmp, ns);

  get_value_set_rec(tmp, dest, "", tmp.type(), ns);
}

/*******************************************************************\

Function: value_sett::get_value_set_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::get_value_set_rec(
  const exprt &expr,
  object_mapt &dest,
  const std::string &suffix,
  const typet &original_type,
  const namespacet &ns) const
{
  #if 0
  std::cout << "GET_VALUE_SET_REC EXPR: " << from_expr(ns, "", expr) << std::endl;
  std::cout << "GET_VALUE_SET_REC SUFFIX: " << suffix << std::endl;
  std::cout << std::endl;
  #endif
  
  const typet &expr_type=ns.follow(expr.type());

  if(expr.id()==ID_unknown || expr.id()==ID_invalid)
  {
    insert(dest, exprt(ID_unknown, original_type));
  }
  else if(expr.id()==ID_index)
  {
    assert(expr.operands().size()==2);

    const typet &type=ns.follow(expr.op0().type());

    assert(type.id()==ID_array ||
           type.id()==ID_incomplete_array);
           
    get_value_set_rec(expr.op0(), dest, "[]"+suffix, original_type, ns);
  }
  else if(expr.id()==ID_member)
  {
    assert(expr.operands().size()==1);

    const typet &type=ns.follow(expr.op0().type());

    assert(type.id()==ID_struct ||
           type.id()==ID_union ||
           type.id()==ID_incomplete_struct ||
           type.id()==ID_incomplete_union);
           
    const std::string &component_name=
      expr.get_string(ID_component_name);
    
    get_value_set_rec(expr.op0(), dest,
      "."+component_name+suffix, original_type, ns);
  }
  else if(expr.id()==ID_symbol)
  {
    // is it a pointer, integer, array or struct?
    if(expr_type.id()==ID_pointer ||
       expr_type.id()==ID_signedbv ||
       expr_type.id()==ID_unsignedbv ||
       expr_type.id()==ID_struct ||
       expr_type.id()==ID_union ||
       expr_type.id()==ID_array)
    {
      // look it up
      valuest::const_iterator v_it=
        values.find(expr.get_string(ID_identifier)+suffix);

      // not found? try without suffix
      if(v_it==values.end())
        v_it=values.find(expr.get_string(ID_identifier));
        
      if(v_it!=values.end())
        make_union(dest, v_it->second.object_map);
      else
        insert(dest, exprt(ID_unknown, original_type));
    }
    else
      insert(dest, exprt(ID_unknown, original_type));
  }
  else if(expr.id()==ID_if)
  {
    if(expr.operands().size()!=3)
      throw "if takes three operands";

    get_value_set_rec(expr.op1(), dest, suffix, original_type, ns);
    get_value_set_rec(expr.op2(), dest, suffix, original_type, ns);
  }
  else if(expr.id()==ID_address_of)
  {
    if(expr.operands().size()!=1)
      throw expr.id_string()+" expected to have one operand";
      
    get_reference_set(expr.op0(), dest, ns);
  }
  else if(expr.id()==ID_dereference)
  {
    object_mapt reference_set;
    get_reference_set(expr, reference_set, ns);
    const object_map_dt &object_map=reference_set.read();
    
    if(object_map.begin()==object_map.end())
      insert(dest, exprt(ID_unknown, original_type));
    else
    {
      for(object_map_dt::const_iterator
          it1=object_map.begin();
          it1!=object_map.end();
          it1++)
      {
        const exprt &object=object_numbering[it1->first];
        get_value_set_rec(object, dest, suffix, original_type, ns);
      }
    }
  }
  else if(expr.id()=="reference_to")
  {
    // old stuff, will go away
    object_mapt reference_set;
    
    get_reference_set(expr, reference_set, ns);
    
    const object_map_dt &object_map=reference_set.read();
 
    if(object_map.begin()==object_map.end())
      insert(dest, exprt(ID_unknown, original_type));
    else
    {
      for(object_map_dt::const_iterator
          it=object_map.begin();
          it!=object_map.end();
          it++)
      {
        const exprt &object=object_numbering[it->first];
        get_value_set_rec(object, dest, suffix, original_type, ns);
      }
    }
  }
  else if(expr.is_constant())
  {
    // check if NULL
    if(expr.get(ID_value)==ID_NULL &&
       expr_type.id()==ID_pointer)
    {
      insert(dest, exprt("NULL-object", expr_type.subtype()), 0);
    }
    else if(expr_type.id()==ID_unsignedbv ||
            expr_type.id()==ID_signedbv)
    {
      // an integer constant got turned into a pointer
      insert(dest, exprt(ID_integer_address, uchar_type()));
    }
    else
      insert(dest, exprt(ID_unknown, original_type));
  }
  else if(expr.id()==ID_typecast)
  {
    if(expr.operands().size()!=1)
      throw "typecast takes one operand";
      
    // let's see what gets converted to what
    
    const typet &op_type=ns.follow(expr.op0().type());
    
    if(op_type.id()==ID_pointer)
    {
      // pointer-to-pointer -- we just ignore these
      get_value_set_rec(expr.op0(), dest, suffix, original_type, ns);
    }
    else if(op_type.id()==ID_unsignedbv ||
            op_type.id()==ID_signedbv)
    {
      // integer-to-pointer
      
      if(expr.op0().is_zero())
        insert(dest, exprt("NULL-object", expr_type.subtype()), 0);
      else
      {
        // see if we have something for the integer
        object_mapt tmp;
                
        get_value_set_rec(expr.op0(), tmp, suffix, original_type, ns);

        if(tmp.read().size()==0)
        {
          // if not, throw in integer
          insert(dest, exprt(ID_integer_address, uchar_type()));        
        }
        else if(tmp.read().size()==1 &&
                object_numbering[tmp.read().begin()->first].id()==ID_unknown)
        {
          // if not, throw in integer
          insert(dest, exprt(ID_integer_address, uchar_type()));        
        }
        else
        {
          // use as is
          dest.write().insert(tmp.read().begin(), tmp.read().end());
        }
      }
    }
    else
      insert(dest, exprt(ID_unknown, original_type));
  }
  else if(expr.id()==ID_plus ||
          expr.id()==ID_minus)
  {
    if(expr.operands().size()<2)
      throw expr.id_string()+" expected to have at least two operands";

    object_mapt pointer_expr_set;
    mp_integer i;
    bool i_is_set=false;

    // special case for pointer+integer

    if(expr.operands().size()==2 &&
       expr_type.id()==ID_pointer)
    {
      exprt ptr_operand;
      
      if(expr.op0().type().id()!=ID_pointer &&
         expr.op0().is_constant())
      {
        i_is_set=!to_integer(expr.op0(), i);
        ptr_operand=expr.op1();
      }
      else
      {
        i_is_set=!to_integer(expr.op1(), i);
        ptr_operand=expr.op0();
      }
        
      if(i_is_set)
      {
        i*=pointer_offset_size(ns, ptr_operand.type().subtype());

        if(expr.id()==ID_minus) i.negate();
      }

      get_value_set_rec(
        ptr_operand, pointer_expr_set, "", ptr_operand.type(), ns);
    }
    else
    {
      // we get the points-to for all operands, even integers
      forall_operands(it, expr)
      {
        get_value_set_rec(
          *it, pointer_expr_set, "", it->type(), ns);
      }
    }

    for(object_map_dt::const_iterator
        it=pointer_expr_set.read().begin();
        it!=pointer_expr_set.read().end();
        it++)
    {
      objectt object=it->second;

      // adjust by offset      
      if(object.offset_is_zero() && i_is_set)
        object.offset=i;
      else
        object.offset_is_set=false;
        
      insert(dest, it->first, object);
    }
  }
  else if(expr.id()==ID_mult)
  {
    // this is to do stuff like
    // (int*)((sel*(ulong)&a)+((sel^0x1)*(ulong)&b))
    
    if(expr.operands().size()<2)
      throw expr.id_string()+" expected to have at least two operands";

    object_mapt pointer_expr_set;

    // we get the points-to for all operands, even integers
    forall_operands(it, expr)
    {
      get_value_set_rec(
        *it, pointer_expr_set, "", it->type(), ns);
    }

    for(object_map_dt::const_iterator
        it=pointer_expr_set.read().begin();
        it!=pointer_expr_set.read().end();
        it++)
    {
      objectt object=it->second;

      // kill any offset
      object.offset_is_set=false;
        
      insert(dest, it->first, object);
    }
  }
  else if(expr.id()==ID_sideeffect)
  {
    const irep_idt &statement=expr.get(ID_statement);
    
    if(statement==ID_function_call)
    {
      // these should be gone
      throw "unexpected function_call sideeffect";
    }
    else if(statement==ID_malloc)
    {
      assert(suffix=="");
      
      const typet &dynamic_type=
        static_cast<const typet &>(expr.find("#type"));

      dynamic_object_exprt dynamic_object(dynamic_type);
      dynamic_object.instance()=from_integer(location_number, typet(ID_natural));
      dynamic_object.valid()=true_exprt();

      insert(dest, dynamic_object, 0);
    }
    else if(statement==ID_cpp_new ||
            statement==ID_cpp_new_array)
    {
      assert(suffix=="");
      assert(expr_type.id()==ID_pointer);

      dynamic_object_exprt dynamic_object(expr_type.subtype());
      dynamic_object.instance()=from_integer(location_number, typet(ID_natural));
      dynamic_object.valid()=true_exprt();

      insert(dest, dynamic_object, 0);
    }
    else
      insert(dest, exprt(ID_unknown, original_type));
  }
  else if(expr.id()==ID_struct)
  {
    // a struct constructor, which may contain addresses
    forall_operands(it, expr)
      get_value_set_rec(*it, dest, suffix, original_type, ns);
  }
  else if(expr.id()==ID_with)
  {
    assert(expr.operands().size()==3);

    // this is the array/struct
    object_mapt tmp_map0;
    get_value_set_rec(expr.op0(), tmp_map0, suffix, original_type, ns);

    // this is the update value -- note NO SUFFIX
    object_mapt tmp_map2;
    get_value_set_rec(expr.op2(), tmp_map2, "", original_type, ns);

    if(expr_type.id()==ID_struct)
    {
      #if 0
      const object_map_dt &object_map0=tmp_map0.read();
      irep_idt component_name=expr.op1().get(ID_component_name);

      bool insert=true;

      for(object_map_dt::const_iterator
          it=object_map0.begin();
          it!=object_map0.end();
          it++)
      {
        const exprt &e=to_expr(it);

        if(e.id()==ID_member &&
           e.get(ID_component_name)==component_name)
        {
          if(insert)
          {
            dest.write().insert(tmp_map2.read().begin(), tmp_map2.read().end());
            insert=false;
          }
        }
        else
          dest.write().insert(*it);
      }
      #else
      // Should be more precise! We only want "suffix"
      make_union(dest, tmp_map0);
      make_union(dest, tmp_map2);
      #endif
    }
    else
    {
      make_union(dest, tmp_map0);
      make_union(dest, tmp_map2);
    }
  }
  else if(expr.id()==ID_array)
  {
    // an array constructur, possibly containing addresses
    forall_operands(it, expr)
      get_value_set_rec(*it, dest, suffix, original_type, ns);
  }
  else if(expr.id()==ID_array_of)
  {
    // an array constructor, possibly containing an address
    assert(expr.operands().size()==1);
    get_value_set_rec(expr.op0(), dest, suffix, original_type, ns);
  }
  else if(expr.id()==ID_dynamic_object)
  {
    const dynamic_object_exprt &dynamic_object=
      to_dynamic_object_expr(expr);
      
    const std::string prefix=
      "value_set::dynamic_object"+
      dynamic_object.instance().get_string(ID_value);

    // first try with suffix
    const std::string full_name=prefix+suffix;
  
    // look it up
    valuest::const_iterator v_it=values.find(full_name);
    
    // not found? try without suffix
    if(v_it==values.end())
      v_it=values.find(prefix);

    if(v_it==values.end())
      insert(dest, exprt(ID_unknown, original_type));
    else
      make_union(dest, v_it->second.object_map);
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    if(expr.operands().size()!=2)
      throw "byte_extract takes two operands";
      
    // we just pass through
    get_value_set_rec(expr.op0(), dest, suffix, original_type, ns);
  }
  else if(expr.id()==ID_byte_update_little_endian ||
          expr.id()==ID_byte_update_big_endian)
  {
    if(expr.operands().size()!=3)
      throw "byte_update takes three operands";
      
    // we just pass through
    get_value_set_rec(expr.op0(), dest, suffix, original_type, ns);
    get_value_set_rec(expr.op2(), dest, suffix, original_type, ns);
    
    // we could have checked object size to be more precise
  }
  else
  {
    #if 0
    std::cout << "WARNING: not doing " << expr.id() << std::endl;
    #endif
  }

  #if 0
  std::cout << "GET_VALUE_SET_REC RESULT:";
  for(object_map_dt::const_iterator
      it=dest.read().begin();
      it!=dest.read().end();
      it++)
  {
    const exprt &e=to_expr(it);
    std::cout << " " << from_expr(ns, "", e);
  }
  std::cout << std::endl << std::endl;
  #endif
}

/*******************************************************************\

Function: value_sett::dereference_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::dereference_rec(
  const exprt &src,
  exprt &dest) const
{
  // remove pointer typecasts
  if(src.id()==ID_typecast)
  {
    assert(src.type().id()==ID_pointer);

    if(src.operands().size()!=1)
      throw "typecast expects one operand";
    
    dereference_rec(src.op0(), dest);
  }
  else
    dest=src;
}

/*******************************************************************\

Function: value_sett::get_reference_set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::get_reference_set(
  const exprt &expr,
  value_setst::valuest &dest,
  const namespacet &ns) const
{
  object_mapt object_map;
  get_reference_set(expr, object_map, ns);
  
  for(object_map_dt::const_iterator
      it=object_map.read().begin();
      it!=object_map.read().end();
      it++)
    dest.push_back(to_expr(it));
}

/*******************************************************************\

Function: value_sett::get_reference_set_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::get_reference_set_rec(
  const exprt &expr,
  object_mapt &dest,
  const namespacet &ns) const
{
  #if 0
  std::cout << "GET_REFERENCE_SET_REC EXPR: " << from_expr(ns, "", expr) << std::endl;
  #endif

  if(expr.id()==ID_symbol ||
     expr.id()==ID_dynamic_object ||
     expr.id()==ID_string_constant)
  {
    if(expr.type().id()==ID_array &&
       expr.type().subtype().id()==ID_array)
      insert(dest, expr);
    else    
      insert(dest, expr, 0);

    return;
  }
  else if(expr.id()==ID_dereference)
  {
    if(expr.operands().size()!=1)
      throw expr.id_string()+" expected to have one operand";

    get_value_set_rec(expr.op0(), dest, "", expr.op0().type(), ns);

    #if 0
    for(expr_sett::const_iterator it=value_set.begin(); it!=value_set.end(); it++)
      std::cout << "VALUE_SET: " << from_expr(ns, "", *it) << std::endl;
    #endif

    return;
  }
  else if(expr.id()==ID_index)
  {
    if(expr.operands().size()!=2)
      throw "index expected to have two operands";
  
    const index_exprt &index_expr=to_index_expr(expr);
    const exprt &array=index_expr.array();
    const exprt &offset=index_expr.index();
    const typet &array_type=ns.follow(array.type());
    
    assert(array_type.id()==ID_array ||
           array_type.id()==ID_incomplete_array);
    
    object_mapt array_references;
    get_reference_set(array, array_references, ns);
        
    const object_map_dt &object_map=array_references.read();
    
    for(object_map_dt::const_iterator
        a_it=object_map.begin();
        a_it!=object_map.end();
        a_it++)
    {
      const exprt &object=object_numbering[a_it->first];

      if(object.id()==ID_unknown)
        insert(dest, exprt(ID_unknown, expr.type()));
      else
      {
        index_exprt index_expr(expr.type());
        index_expr.array()=object;
        index_expr.index()=gen_zero(index_type());
        
        // adjust type?
        if(ns.follow(object.type())!=array_type)
          index_expr.make_typecast(array.type());
        
        objectt o=a_it->second;
        mp_integer i;

        if(offset.is_zero())
        {
        }
        else if(!to_integer(offset, i) &&
                o.offset_is_zero())
          o.offset=i*pointer_offset_size(ns, array_type.subtype());
        else
          o.offset_is_set=false;
          
        insert(dest, index_expr, o);
      }
    }
    
    return;
  }
  else if(expr.id()==ID_member)
  {
    const irep_idt &component_name=expr.get(ID_component_name);

    if(expr.operands().size()!=1)
      throw "member expected to have one operand";
  
    const exprt &struct_op=expr.op0();
    
    object_mapt struct_references;
    get_reference_set(struct_op, struct_references, ns);
    
    const object_map_dt &object_map=struct_references.read();

    for(object_map_dt::const_iterator
        it=object_map.begin();
        it!=object_map.end();
        it++)
    {
      const exprt &object=object_numbering[it->first];
      
      if(object.id()==ID_unknown)
        insert(dest, exprt(ID_unknown, expr.type()));
      else
      {
        objectt o=it->second;

        member_exprt member_expr(expr.type());
        member_expr.op0()=object;
        member_expr.set_component_name(component_name);
        
        // We cannot introduce a cast from scalar to non-scalar,
        // thus, we can only adjust the types of structs and unions. 
        
        const typet& final_object_type = ns.follow(object.type());
        
        if(final_object_type.id()==ID_struct ||
           final_object_type.id()==ID_union)
        {
          // adjust type?
          if(ns.follow(struct_op.type())!=final_object_type)
            member_expr.op0().make_typecast(struct_op.type());
          
          insert(dest, member_expr, o);       
        }
        else
          insert(dest, exprt(ID_unknown, expr.type()));
      }
    }

    return;
  }
  else if(expr.id()==ID_if)
  {
    if(expr.operands().size()!=3)
      throw "if takes three operands";

    get_reference_set_rec(expr.op1(), dest, ns);
    get_reference_set_rec(expr.op2(), dest, ns);
    return;
  }

  insert(dest, exprt(ID_unknown, expr.type()));
}

/*******************************************************************\

Function: value_sett::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::assign(
  const exprt &lhs,
  const exprt &rhs,
  const namespacet &ns,
  bool add_to_sets)
{
  #if 0
  std::cout << "ASSIGN LHS: " << from_expr(ns, "", lhs) << std::endl;
  std::cout << "ASSIGN RHS: " << from_expr(ns, "", rhs) << std::endl;
  output(ns, std::cout);
  #endif

  const typet &type=ns.follow(lhs.type());

  if(type.id()==ID_struct ||
     type.id()==ID_union)
  {
    const struct_union_typet &struct_union_type=
      to_struct_union_type(type);
    
    for(struct_union_typet::componentst::const_iterator
        c_it=struct_union_type.components().begin();
        c_it!=struct_union_type.components().end();
        c_it++)
    {
      const typet &subtype=c_it->type();
      const irep_idt &name=c_it->get(ID_name);

      // ignore methods and padding
      if(subtype.id()==ID_code ||
         c_it->get_is_padding()) continue;
    
      member_exprt lhs_member(subtype);
      lhs_member.set_component_name(name);
      lhs_member.op0()=lhs;

      exprt rhs_member;

      if(rhs.id()==ID_unknown ||
         rhs.id()==ID_invalid)
      {
        rhs_member=exprt(rhs.id(), subtype);
      }
      else
      {
        if(!base_type_eq(rhs.type(), type, ns))
          assert(false);

        rhs_member=make_member(rhs, name, ns);
      
        assign(lhs_member, rhs_member, ns, add_to_sets);
      }
    }
  }
  else if(type.id()==ID_array)
  {
    exprt lhs_index(ID_index, type.subtype());
    lhs_index.copy_to_operands(lhs, exprt(ID_unknown, index_type()));

    if(rhs.id()==ID_unknown ||
       rhs.id()==ID_invalid)
    {
      assign(lhs_index, exprt(rhs.id(), type.subtype()), ns, add_to_sets);
    }
    else
    {
      std::cout << "RHS: " << rhs.type().pretty() << std::endl;
      std::cout << "TTT: " << type.pretty() << std::endl;
      assert(base_type_eq(rhs.type(), type, ns));
        
      if(rhs.id()==ID_array_of)
      {
        assert(rhs.operands().size()==1);
        assign(lhs_index, rhs.op0(), ns, add_to_sets);
      }
      else if(rhs.id()==ID_array ||
              rhs.id()==ID_constant)
      {
        forall_operands(o_it, rhs)
        {
          assign(lhs_index, *o_it, ns, add_to_sets);
          add_to_sets=true;
        }
      }
      else if(rhs.id()==ID_with)
      {
        assert(rhs.operands().size()==3);

        exprt op0_index(ID_index, type.subtype());
        op0_index.copy_to_operands(rhs.op0(), exprt(ID_unknown, index_type()));

        assign(lhs_index, op0_index, ns, add_to_sets);
        assign(lhs_index, rhs.op2(), ns, true);
      }
      else
      {
        exprt rhs_index(ID_index, type.subtype());
        rhs_index.copy_to_operands(rhs, exprt(ID_unknown, index_type()));
        assign(lhs_index, rhs_index, ns, true);
      }
    }
  }
  else
  {
    // basic type
    object_mapt values_rhs;
    get_value_set(rhs, values_rhs, ns);
    
    assign_rec(lhs, values_rhs, "", ns, add_to_sets);
  }
}

/*******************************************************************\

Function: value_sett::do_free

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::do_free(
  const exprt &op,
  const namespacet &ns)
{
  // op must be a pointer
  if(op.type().id()!=ID_pointer)
    throw "free expected to have pointer-type operand";

  // find out what it points to    
  object_mapt value_set;
  get_value_set(op, value_set, ns);
  
  const object_map_dt &object_map=value_set.read();
  
  // find out which *instances* interest us
  expr_sett to_mark;
  
  for(object_map_dt::const_iterator
      it=object_map.begin();
      it!=object_map.end();
      it++)
  {
    const exprt &object=object_numbering[it->first];

    if(object.id()==ID_dynamic_object)
    {
      const dynamic_object_exprt &dynamic_object=
        to_dynamic_object_expr(object);
      
      if(dynamic_object.valid().is_true())
        to_mark.insert(dynamic_object.instance());
    }
  }
  
  // mark these as 'may be invalid'
  // this, unfortunately, destroys the sharing
  for(valuest::iterator v_it=values.begin();
      v_it!=values.end();
      v_it++)
  {
    object_mapt new_object_map;

    const object_map_dt &old_object_map=
      v_it->second.object_map.read();
      
    bool changed=false;
    
    for(object_map_dt::const_iterator
        o_it=old_object_map.begin();
        o_it!=old_object_map.end();
        o_it++)
    {
      const exprt &object=object_numbering[o_it->first];

      if(object.id()==ID_dynamic_object)
      {
        const exprt &instance=
          to_dynamic_object_expr(object).instance();

        if(to_mark.count(instance)==0)
          set(new_object_map, o_it);
        else
        {
          // adjust
          objectt o=o_it->second;
          exprt tmp(object);
          to_dynamic_object_expr(tmp).valid()=exprt(ID_unknown);
          insert(new_object_map, tmp, o);
          changed=true;
        }
      }
      else
        set(new_object_map, o_it);
    }
    
    if(changed)
      v_it->second.object_map=new_object_map;
  }
}

/*******************************************************************\

Function: value_sett::assign_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::assign_rec(
  const exprt &lhs,
  const object_mapt &values_rhs,
  const std::string &suffix,
  const namespacet &ns,
  bool add_to_sets)
{
  #if 0
  std::cout << "ASSIGN_REC LHS: " << from_expr(ns, "", lhs) << std::endl;
  std::cout << "ASSIGN_REC LHS ID: " << lhs.id() << std::endl;
  std::cout << "ASSIGN_REC SUFFIX: " << suffix << std::endl;

  for(object_map_dt::const_iterator it=values_rhs.read().begin(); 
      it!=values_rhs.read().end(); 
      it++)
    std::cout << "ASSIGN_REC RHS: " << 
      from_expr(ns, "", object_numbering[it->first]) << std::endl;
  std::cout << std::endl;
  #endif
  
  if(lhs.id()==ID_symbol)
  {
    const irep_idt &identifier=lhs.get(ID_identifier);
    
    entryt &e=get_entry(entryt(identifier, suffix), lhs.type());
    
    if(add_to_sets)
      make_union(e.object_map, values_rhs);
    else
      e.object_map=values_rhs;
  }
  else if(lhs.id()==ID_dynamic_object)
  {
    const dynamic_object_exprt &dynamic_object=
      to_dynamic_object_expr(lhs);
  
    const std::string name=
      "value_set::dynamic_object"+
      dynamic_object.instance().get_string(ID_value);
      
    entryt &e=get_entry(entryt(name, suffix), lhs.type());

    make_union(e.object_map, values_rhs);
  }
  else if(lhs.id()==ID_dereference)
  {
    if(lhs.operands().size()!=1)
      throw lhs.id_string()+" expected to have one operand";
      
    object_mapt reference_set;
    get_reference_set(lhs, reference_set, ns);
    
    if(reference_set.read().size()!=1)
      add_to_sets=true;
      
    for(object_map_dt::const_iterator
        it=reference_set.read().begin();
        it!=reference_set.read().end();
        it++)
    {
      const exprt &object=object_numbering[it->first];

      if(object.id()!=ID_unknown)
        assign_rec(object, values_rhs, suffix, ns, add_to_sets);
    }
  }
  else if(lhs.id()==ID_index)
  {
    if(lhs.operands().size()!=2)
      throw "index expected to have two operands";
      
    const typet &type=ns.follow(lhs.op0().type());
      
    assert(type.id()==ID_array || type.id()==ID_incomplete_array);

    assign_rec(lhs.op0(), values_rhs, "[]"+suffix, ns, true);
  }
  else if(lhs.id()==ID_member)
  {
    if(lhs.operands().size()!=1)
      throw "member expected to have one operand";
  
    const std::string &component_name=lhs.get_string(ID_component_name);

    const typet &type=ns.follow(lhs.op0().type());

    assert(type.id()==ID_struct ||
           type.id()==ID_union ||
           type.id()==ID_incomplete_struct ||
           type.id()==ID_incomplete_union);
           
    assign_rec(lhs.op0(), values_rhs, "."+component_name+suffix, ns, add_to_sets);
  }
  else if(lhs.id()=="valid_object" ||
          lhs.id()=="dynamic_size" ||
          lhs.id()=="dynamic_type" ||
          lhs.id()=="is_zero_string" ||
          lhs.id()=="zero_string" ||
          lhs.id()=="zero_string_length")
  {
    // we ignore this here
  }
  else if(lhs.id()==ID_string_constant)
  {
    // someone writes into a string-constant
    // evil guy
  }
  else if(lhs.id()=="NULL-object")
  {
    // evil as well
  }
  else if(lhs.id()==ID_typecast)
  {
    const typecast_exprt &typecast_expr=to_typecast_expr(lhs);
  
    assign_rec(typecast_expr.op(), values_rhs, suffix, ns, add_to_sets);
  }
  else if(lhs.id()==ID_byte_extract_little_endian ||
          lhs.id()==ID_byte_extract_big_endian)
  {
    assert(lhs.operands().size()==2);
    assign_rec(lhs.op0(), values_rhs, suffix, ns, true);
  }
  else if(lhs.id()==ID_integer_address)
  {
    // that's like assigning into __CPROVER_memory[...],
    // which we don't track
  }
  else
    throw "assign NYI: `"+lhs.id_string()+"'";
}

/*******************************************************************\

Function: value_sett::do_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::do_function_call(
  const irep_idt &function,
  const exprt::operandst &arguments,
  const namespacet &ns)
{
  const symbolt &symbol=ns.lookup(function);

  const code_typet &type=to_code_type(symbol.type);
  const code_typet::argumentst &argument_types=type.arguments();

  // these first need to be assigned to dummy, temporary arguments
  // and only thereafter to the actuals, in order
  // to avoid overwriting actuals that are needed for recursive
  // calls

  for(unsigned i=0; i<arguments.size(); i++)
  {
    const std::string identifier="value_set::dummy_arg_"+i2string(i);
    exprt dummy_lhs=symbol_exprt(identifier, arguments[i].type());
    assign(dummy_lhs, arguments[i], ns, false);
  }

  // now assign to 'actual actuals'

  unsigned i=0;

  for(code_typet::argumentst::const_iterator
      it=argument_types.begin();
      it!=argument_types.end();
      it++)
  {
    const irep_idt &identifier=it->get_identifier();
    if(identifier=="") continue;

    const exprt v_expr=
      symbol_exprt("value_set::dummy_arg_"+i2string(i), it->type());
    
    exprt actual_lhs=symbol_exprt(identifier, it->type());
    assign(actual_lhs, v_expr, ns, true);
    i++;
  }

  // we could delete the dummy_arg_* now.
}

/*******************************************************************\

Function: value_sett::do_end_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::do_end_function(
  const exprt &lhs,
  const namespacet &ns)
{
  if(lhs.is_nil()) return;

  symbol_exprt rhs("value_set::return_value", lhs.type());

  assign(lhs, rhs, ns);
}

/*******************************************************************\

Function: value_sett::apply_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::apply_code(
  const codet &code,
  const namespacet &ns)
{
  const irep_idt &statement=code.get(ID_statement);

  if(statement==ID_block)
  {
    forall_operands(it, code)
      apply_code(to_code(*it), ns);
  }
  else if(statement==ID_function_call)
  {
    // shouldn't be here
    assert(false);
  }
  else if(statement==ID_assign ||
          statement==ID_init)
  {
    if(code.operands().size()!=2)
      throw "assignment expected to have two operands";

    assign(code.op0(), code.op1(), ns);
  }
  else if(statement==ID_decl)
  {
    if(code.operands().size()!=1)
      throw "decl expected to have one operand";

    const exprt &lhs=code.op0();

    if(lhs.id()!=ID_symbol)
      throw "decl expected to have symbol on lhs";
      
    const typet &lhs_type=ns.follow(lhs.type());

    if(lhs_type.id()==ID_pointer ||
       (lhs_type.id()==ID_array &&
        ns.follow(lhs_type.subtype()).id()==ID_pointer))
    {
      // assign the address of the failed object
      exprt failed=get_failed_symbol(to_symbol_expr(lhs), ns);
      
      if(failed.is_not_nil())
      {
        address_of_exprt address_of_expr;
        address_of_expr.object()=failed;
        address_of_expr.type()=lhs.type();
        assign(lhs, address_of_expr, ns);
      }
      else
        assign(lhs, exprt(ID_invalid), ns);
    }
  }
  else if(statement=="specc_notify" ||
          statement=="specc_wait")
  {
    // ignore, does not change variables
  }
  else if(statement==ID_expression)
  {
    // can be ignored, we don't expect sideeffects here
  }
  else if(statement=="cpp_delete" ||
          statement=="cpp_delete[]")
  {
    // does nothing
  }
  else if(statement==ID_free)
  {
    // this may kill a valid bit

    if(code.operands().size()!=1)
      throw "free expected to have one operand";

    do_free(code.op0(), ns);
  }
  else if(statement=="lock" || statement=="unlock")
  {
    // ignore for now
  }
  else if(statement==ID_asm)
  {
    // ignore for now, probably not safe
  }
  else if(statement==ID_nondet)
  {
    // doesn't do anything
  }
  else if(statement==ID_printf)
  {
    // doesn't do anything
  }
  else if(statement==ID_return)
  {
    // this is turned into an assignment
    if(code.operands().size()==1)
    {
      symbol_exprt lhs("value_set::return_value", code.op0().type());
      assign(lhs, code.op0(), ns);
    }
  }
  else if(statement==ID_array_set)
  {
  }
  else if(statement==ID_array_copy)
  {
  }
  else if(statement==ID_assume)
  {
    guard(to_code_assume(code).op0(), ns);
  }
  else if(statement==ID_user_specified_predicate || statement==ID_user_specified_parameter_predicates || statement == ID_user_specified_return_predicates)
  {
    // doesn't do anything
  }
  else
  {
    std::cerr << code.pretty() << std::endl;
    throw "value_sett: unexpected statement: "+id2string(statement);
  }
}

/*******************************************************************\

Function: value_sett::guard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::guard(
  const exprt &expr,
  const namespacet &ns)
{
  if(expr.id()==ID_and)
  {
    forall_operands(it, expr)
      guard(*it, ns);
  }
  else if(expr.id()==ID_equal)
  {
  }
  else if(expr.id()==ID_notequal)
  {
  }
  else if(expr.id()==ID_not)
  {
  }
  else if(expr.id()==ID_dynamic_object)
  {
    assert(expr.operands().size()==1);

    dynamic_object_exprt dynamic_object(uchar_type());
    //dynamic_object.instance()=from_integer(location_number, typet(ID_natural));
    dynamic_object.valid()=true_exprt();

    address_of_exprt address_of(dynamic_object);
    address_of.type()=expr.op0().type();

    assign(expr.op0(), address_of, ns);
  }
}

/*******************************************************************\

Function: value_sett::make_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt value_sett::make_member(
  const exprt &src,
  const irep_idt &component_name,
  const namespacet &ns)
{
  const struct_union_typet &struct_union_type=
    to_struct_union_type(ns.follow(src.type()));

  if(src.id()==ID_struct ||
     src.id()==ID_constant)
  {
    unsigned no=struct_union_type.component_number(component_name);
    assert(no<src.operands().size());
    return src.operands()[no];
  }
  else if(src.id()==ID_with)
  {
    assert(src.operands().size()==3);

    // see if op1 is the member we want
    const exprt &member_operand=src.op1();

    if(component_name==member_operand.get(ID_component_name))
      // yes! just take op2
      return src.op2();
    else
      // no! do this recursively
      return make_member(src.op0(), component_name, ns);
  }
  else if(src.id()==ID_typecast)
  {
    // push through typecast
    assert(src.operands().size()==1);
    return make_member(src.op0(), component_name, ns);
  }

  // give up
  typet subtype=struct_union_type.component_type(component_name);
  member_exprt member_expr(subtype);
  member_expr.op0()=src;
  member_expr.set_component_name(component_name);

  return member_expr;
}

