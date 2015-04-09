/*******************************************************************\

Module: Value Set (Flow Insensitive, Validity Regions)

Author: Daniel Kroening, kroening@kroening.com,
        CM Wintersteiger

\*******************************************************************/

#include <cassert>
#include <iostream>

#include <util/symbol_table.h>
#include <util/simplify_expr.h>
#include <util/expr_util.h>
#include <util/base_type.h>
#include <util/std_expr.h>
#include <util/i2string.h>
#include <util/prefix.h>
#include <util/std_code.h>
#include <util/arith_tools.h>

#include <langapi/language_util.h>
#include <ansi-c/c_types.h>

#include "value_set_fivrns.h"

const value_set_fivrnst::object_map_dt value_set_fivrnst::object_map_dt::empty;
object_numberingt value_set_fivrnst::object_numbering;
hash_numbering<irep_idt, irep_id_hash> value_set_fivrnst::function_numbering;

static std::string alloc_adapter_prefix = "alloc_adaptor::";

#define forall_objects(it, map) \
  for(object_map_dt::const_iterator (it) = (map).begin(); \
  (it)!=(map).end(); \
  (it)++)

#define forall_valid_objects(it, map) \
  for(object_map_dt::const_iterator (it) = (map).begin(); \
  (it)!=(map).end(); \
  (it)++) \
   if((map).is_valid_at((it)->first, from_function, from_target_index))

#define Forall_objects(it, map) \
  for(object_map_dt::iterator (it) = (map).begin(); \
  (it)!=(map).end(); \
  (it)++)

#define Forall_valid_objects(it, map) \
  for(object_map_dt::iterator (it) = (map).begin(); \
  (it)!=(map).end(); \
  (it)++) \
   if((map).is_valid_at((it)->first, from_function, from_target_index))

/*******************************************************************\

Function: value_set_fivrnst::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_fivrnst::output(
  const namespacet &ns,
  std::ostream &out) const
{
  for(valuest::const_iterator
      v_it=values.begin();
      v_it!=values.end();
      v_it++)
    output_entry(v_it->second, ns, out);
}

/*******************************************************************\

Function: value_set_fivrnst::output_entry

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_fivrnst::output_entry(
  const entryt &e,
  const namespacet &ns,
  std::ostream &out) const
{
  irep_idt identifier, display_name;
//  if(has_prefix(id2string(e.identifier), "value_set::dynamic_object"))
//  {
//    display_name=id2string(e.identifier)+e.suffix;
//    identifier="";
//  }
//  else if(e.identifier=="value_set::return_value")
//  {
//    display_name="RETURN_VALUE"+e.suffix;
//    identifier="";
//  }
//  else
  {
    #if 0
    const symbolt &symbol=ns.lookup(id2string(e.identifier));
    display_name=symbol.display_name()+e.suffix;
    identifier=symbol.name;
    #else      
    display_name=id2string(e.identifier)+e.suffix;
    #endif
  }
  
  const object_mapt &object_map=e.object_map;
  
  out << display_name << " = { ";
  if(object_map.read().size()!=0) out << std::endl << "      ";
  
  unsigned width=0;
  
  forall_valid_objects(o_it, object_map.read())
  {
    const exprt &o=object_numbering[o_it->first];
  
    std::string result="<"; //+i2string(o_it->first) + ",";

    if(o.id()==ID_invalid)
    {
      result+='#';
      result+=", *, "; // offset unknown
      if (o.type().id()==ID_unknown)
        result+='*';
      else if (o.type().id()==ID_invalid)
        result+='#';
      else
        result+=from_type(ns, identifier, o.type());        
      result+='>';
    }
    else if (o.id()==ID_unknown)
    {
      result+='*';
      result+=", *, "; // offset unknown
      if (o.type().id()==ID_unknown)
        result+='*';
      else if (o.type().id()==ID_invalid)
        result+='#';
      else
        result+=from_type(ns, identifier, o.type());        
      result+='>';
    }
    else
    {
      result+=from_expr(ns, identifier, o)+", ";
    
      if(o_it->second.offset_is_set)
        result+=integer2string(o_it->second.offset)+"";
      else
        result+='*';
      
      result+=", ";
      
      if (o.type().id()==ID_unknown)
        result+='*';
      else
      {
        result+=from_type(ns, identifier, o.type());
      }
        
    
      result+='>';
    }

    out << result << std::endl;

    #if 0
    object_map_dt::validity_rangest::const_iterator vr =
      object_map.read().validity_ranges.find(o_it->first);
    
    if (vr != object_map.read().validity_ranges.end())
    {
      if (vr->second.empty())
        std::cout << "        Empty validity record" << std::endl;
      else
        for (object_map_dt::vrange_listt::const_iterator vit =
               vr->second.begin();
             vit!=vr->second.end();
             vit++)
        {
          out << "        valid at " << function_numbering[vit->function] << 
            " [" << vit->from << "," << vit->to << "]";
          if (from_function==vit->function &&
              from_target_index>=vit->from &&
              from_target_index<=vit->to)
            out << " (*)";
          out << std::endl;
        }
    }
    else
    {
      out << "        No validity information" << std::endl;
    }
    #endif

    width+=result.size();
  
    object_map_dt::const_iterator next(o_it);
    next++;

    if(next!=object_map.read().end())
    {
      out << "\n      ";
    }
  }

  out << " } " << std::endl;  
}

/*******************************************************************\

Function: value_set_fivrnst::to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt value_set_fivrnst::to_expr(object_map_dt::const_iterator it) const
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

Function: value_set_fivrnst::make_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_set_fivrnst::make_union(
  object_mapt &dest, 
  const object_mapt &src) const
{
  bool result=false;
  
  forall_objects(it, src.read())
  {    
    if(insert_to(dest, it))
      result=true;
  }
  
  return result;
}

/*******************************************************************\

Function: value_set_fivrnst::make_valid_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_set_fivrnst::make_valid_union(
  object_mapt &dest, 
  const object_mapt &src) const
{
  bool result=false;
  
  forall_valid_objects(it, src.read())
  {    
    if(insert_to(dest, it))
      result=true;
  }
  
  return result;
}

/*******************************************************************\

Function: value_set_fivrnst::copy_objects

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_fivrnst::copy_objects(
  object_mapt &dest, 
  const object_mapt &src) const
{
  forall_valid_objects(it, src.read())
  {
    dest.write()[it->first] = it->second;
    dest.write().validity_ranges[it->first].push_back(
      object_map_dt::validity_ranget(from_function,
                                     from_target_index,
                                     from_target_index));
  }
}

/*******************************************************************\

Function: value_set_fivrnst::get_value_set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_fivrnst::get_value_set(
  const exprt &expr,
  std::list<exprt> &value_set,
  const namespacet &ns) const
{
  object_mapt object_map;
  get_value_set(expr, object_map, ns);
  
  forall_objects(it, object_map.read())
    value_set.push_back(to_expr(it));
  
  #if 0
  for(std::list<exprt>::const_iterator it=value_set.begin(); it!=value_set.end(); it++)
    std::cout << "GET_VALUE_SET: " << from_expr(ns, "", *it) << std::endl;
  #endif
}

/*******************************************************************\

Function: value_set_fivrnst::get_value_set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_fivrnst::get_value_set(
  const exprt &expr,
  object_mapt &dest,
  const namespacet &ns) const
{
  exprt tmp(expr);
  simplify(tmp, ns);

  get_value_set_rec(tmp, dest, "", tmp.type(), ns);
}

/*******************************************************************\

Function: value_set_fivrnst::get_value_set_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_fivrnst::get_value_set_rec(
  const exprt &expr,
  object_mapt &dest,
  const std::string &suffix,
  const typet &original_type,
  const namespacet &ns) const
{
  #if 0
  std::cout << "GET_VALUE_SET_REC EXPR: " << expr << std::endl;
  std::cout << "GET_VALUE_SET_REC SUFFIX: " << suffix << std::endl;
  std::cout << std::endl;
  #endif

  if(expr.id()==ID_unknown || expr.id()==ID_invalid)
  {
    insert_from(dest, exprt(ID_unknown, original_type));
    return;
  }  
  else if(expr.id()==ID_index)
  {
    assert(expr.operands().size()==2);

    const typet &type=ns.follow(expr.op0().type());

    assert(type.id()==ID_array ||
           type.id()==ID_incomplete_array);
           
    get_value_set_rec(expr.op0(), dest, "[]"+suffix, original_type, ns);
    
    return;
  }
  else if(expr.id()==ID_member)
  {
    assert(expr.operands().size()==1);

    if(expr.op0().is_not_nil()) 
    {
      const typet &type=ns.follow(expr.op0().type());
      
      assert(type.id()==ID_struct ||
             type.id()==ID_union ||
             type.id()==ID_incomplete_struct ||
             type.id()==ID_incomplete_union);
             
      const std::string &component_name=
        expr.get_string(ID_component_name);
      
      get_value_set_rec(expr.op0(), dest, "."+component_name+suffix, 
                        original_type, ns);
        
      return;
    }
  }
  else if(expr.id()==ID_symbol)
  {
    // just keep a reference to the ident in the set
    // (if it exists)
    irep_idt ident = expr.get_string(ID_identifier)+suffix;

		if(has_prefix(id2string(ident), alloc_adapter_prefix))
		{
			insert_from(dest, expr, 0);
			return;
		}
		else
		{
			valuest::const_iterator v_it=values.find(ident);
			
			if(v_it!=values.end())
			{
			  copy_objects(dest, v_it->second.object_map);
	      return;
	    }
		}
  }
  else if(expr.id()==ID_if)
  {
    if(expr.operands().size()!=3)
      throw "if takes three operands";

    get_value_set_rec(expr.op1(), dest, suffix, 
                      original_type, ns);
    get_value_set_rec(expr.op2(), dest, suffix, 
                      original_type, ns);

    return;
  }
  else if(expr.id()==ID_address_of)
  {
    if(expr.operands().size()!=1)
      throw expr.id_string()+" expected to have one operand";
      
    get_reference_set(expr.op0(), dest, ns);    
    
    return;
  }
  else if(expr.id()==ID_dereference)
  {
    object_mapt reference_set;
    get_reference_set(expr, reference_set, ns);
    const object_map_dt &object_map=reference_set.read();
    
    if(object_map.begin()!=object_map.end())
    {
      forall_objects(it1, object_map)
      {
        const exprt &object=object_numbering[it1->first];
        get_value_set_rec(object, dest, suffix, 
                          original_type, ns);
      }

      return;
    }
  }
  else if(expr.id()=="reference_to")
  {
    object_mapt reference_set;
    
    get_reference_set(expr, reference_set, ns);
    
    const object_map_dt &object_map=reference_set.read();
 
    if(object_map.begin()!=object_map.end())
    {
      forall_objects(it, object_map)
      {
        const exprt &object=object_numbering[it->first];
        get_value_set_rec(object, dest, suffix, 
                          original_type, ns);
      }

      return;
    }
  }
  else if(expr.is_constant())
  {
    // check if NULL
    if(expr.get(ID_value)==ID_NULL &&
       expr.type().id()==ID_pointer)
    {
      insert_from(dest, exprt("NULL-object", expr.type().subtype()), 0);
      return;
    }
  }
  else if(expr.id()==ID_typecast)
  {
    if(expr.operands().size()!=1)
      throw "typecast takes one operand";

    get_value_set_rec(expr.op0(), dest, suffix, 
                      original_type, ns);
    
    return;
  }
  else if(expr.id()==ID_plus || expr.id()==ID_minus)
  {
    if(expr.operands().size()<2)
      throw expr.id_string()+" expected to have at least two operands";

    if(expr.type().id()==ID_pointer)
    {
      // find the pointer operand
      const exprt *ptr_operand=NULL;

      forall_operands(it, expr)
        if(it->type().id()==ID_pointer)
        {
          if(ptr_operand==NULL)
            ptr_operand=&(*it);
          else
            throw "more than one pointer operand in pointer arithmetic";
        }

      if(ptr_operand==NULL)
        throw "pointer type sum expected to have pointer operand";

      object_mapt pointer_expr_set;
      get_value_set_rec(*ptr_operand, pointer_expr_set, "", 
                        ptr_operand->type(), ns);

      forall_objects(it, pointer_expr_set.read())
      {
        objectt object=it->second;
      
        if(object.offset_is_zero() &&
           expr.operands().size()==2)
        {
          if(expr.op0().type().id()!=ID_pointer)
          {
            mp_integer i;
            if(to_integer(expr.op0(), i))
              object.offset_is_set=false;
            else
              object.offset=(expr.id()==ID_plus)? i : -i;
          }
          else
          {
            mp_integer i;
            if(to_integer(expr.op1(), i))
              object.offset_is_set=false;
            else
              object.offset=(expr.id()==ID_plus)? i : -i;
          }
        }
        else
          object.offset_is_set=false;
          
        insert_from(dest, it->first, object);
      }

      return;
    }
  }
  else if(expr.id()==ID_side_effect)
  {
    const irep_idt &statement=expr.get(ID_statement);
    
    if(statement==ID_function_call)
    {
      // these should be gone
      throw "unexpected function_call sideeffect";
    }
    else if(statement==ID_malloc)
    {
      if(expr.type().id()!=ID_pointer)
        throw "malloc expected to return pointer type";
      
      assert(suffix=="");
      
      const typet &dynamic_type=
        static_cast<const typet &>(expr.find("#type"));

      dynamic_object_exprt dynamic_object(dynamic_type);
      // let's make up a `unique' number for this object...
      dynamic_object.instance()=from_integer( 
                   (from_function << 16) | from_target_index, typet(ID_natural));
      dynamic_object.valid()=true_exprt();

      insert_from(dest, dynamic_object, 0);
      return;          
    }
    else if(statement==ID_cpp_new ||
            statement==ID_cpp_new_array)
    {
      assert(suffix=="");
      assert(expr.type().id()==ID_pointer);

      dynamic_object_exprt dynamic_object(expr.type().subtype());
      // let's make up a unique number for this object...
      dynamic_object.instance()=from_integer( 
                   (from_function << 16) | from_target_index, typet(ID_natural));
      dynamic_object.valid()=true_exprt();

      insert_from(dest, dynamic_object, 0);
      return;
    }
  }
  else if(expr.id()==ID_struct)
  {
    // this is like a static struct object
    insert_from(dest, address_of_exprt(expr), 0);
    return;
  }
  else if(expr.id()==ID_with ||
          expr.id()==ID_array_of ||
          expr.id()==ID_array)
  {
    // these are supposed to be done by assign()
    throw "unexpected value in get_value_set: "+expr.id_string();
  }
  else if(expr.id()==ID_dynamic_object)
  {
    const dynamic_object_exprt &dynamic_object=
      to_dynamic_object_expr(expr);
  
    const std::string name=
      "value_set::dynamic_object"+
      dynamic_object.instance().get_string(ID_value)+
      suffix;
  
    // look it up
    valuest::const_iterator v_it=values.find(name);

    if(v_it!=values.end())
    {
      copy_objects(dest, v_it->second.object_map);
      return;
    }
  }

  insert_from(dest, exprt(ID_unknown, original_type));
}

/*******************************************************************\

Function: value_set_fivrnst::dereference_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_fivrnst::dereference_rec(
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

Function: value_set_fivrnst::get_reference_set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_fivrnst::get_reference_set(
  const exprt &expr,
  expr_sett &dest,
  const namespacet &ns) const
{  
  object_mapt object_map;
  get_reference_set(expr, object_map, ns);    
  
  forall_objects(it, object_map.read())
    dest.insert(to_expr(it));
}

/*******************************************************************\

Function: value_set_fivrnst::get_reference_set_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_fivrnst::get_reference_set_rec(
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
      insert_from(dest, expr);
    else    
      insert_from(dest, expr, 0);

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
    
    const exprt &array=expr.op0();
    const exprt &offset=expr.op1();
    const typet &array_type=ns.follow(array.type());
    
    assert(array_type.id()==ID_array ||
           array_type.id()==ID_incomplete_array);

    
    object_mapt array_references;
    get_reference_set(array, array_references, ns);
    
    const object_map_dt &object_map=array_references.read();
    
    forall_objects(a_it, object_map)
    {
      const exprt &object=object_numbering[a_it->first];

      if(object.id()==ID_unknown)
        insert_from(dest, exprt(ID_unknown, expr.type()));
      else
      {
        exprt index_expr(ID_index, expr.type());
        index_expr.operands().resize(2);
        index_expr.op0()=object;
        index_expr.op1()=gen_zero(index_type());
        
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
          o.offset=i;
        else
          o.offset_is_set=false;
          
        insert_from(dest, index_expr, o);
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

    forall_objects(it, object_map)
    {
      const exprt &object=object_numbering[it->first];
      const typet &obj_type=ns.follow(object.type());
      
      if(object.id()==ID_unknown)
        insert_from(dest, exprt(ID_unknown, expr.type()));
      else if(object.id()==ID_dynamic_object &&
              obj_type.id()!=ID_struct && 
              obj_type.id()!=ID_union)
      {
        // we catch dynamic objects of the wrong type,
        // to avoid non-integral typecasts.        
        insert_from(dest, exprt(ID_unknown, expr.type()));
      }
      else
      {
        objectt o=it->second;

        exprt member_expr(ID_member, expr.type());
        member_expr.copy_to_operands(object);
        member_expr.set(ID_component_name, component_name);
        
        // adjust type?
        if(ns.follow(struct_op.type())!=ns.follow(object.type()))
          member_expr.op0().make_typecast(struct_op.type());
        
        insert_from(dest, member_expr, o);
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

  insert_from(dest, exprt(ID_unknown, expr.type()));
}

/*******************************************************************\

Function: value_set_fivrnst::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_fivrnst::assign(
  const exprt &lhs,
  const exprt &rhs,
  const namespacet &ns,
  bool add_to_sets)
{
  #if 0
  std::cout << "ASSIGN LHS: " << lhs << std::endl;
  std::cout << "ASSIGN LTYPE: " << ns.follow(lhs.type()) << std::endl;
  std::cout << "ASSIGN RHS: " << from_expr(ns, "", rhs) << std::endl;  
  #endif

  if(rhs.id()==ID_if)
  {
    if(rhs.operands().size()!=3)
      throw "if takes three operands";

    assign(lhs, rhs.op1(), ns, add_to_sets);
    assign(lhs, rhs.op2(), ns, true);
    return;
  }

  const typet &type=ns.follow(lhs.type());
  
  if(type.id()==ID_struct ||
     type.id()==ID_union)
  {
    const struct_typet &struct_type=to_struct_type(type);
    
    unsigned no=0;
    
    for(struct_typet::componentst::const_iterator
        c_it=struct_type.components().begin();
        c_it!=struct_type.components().end();
        c_it++, no++)
    {
      const typet &subtype=c_it->type();
      const irep_idt &name=c_it->get(ID_name);

      // ignore methods
      if(subtype.id()==ID_code) continue;
    
      exprt lhs_member(ID_member, subtype);
      lhs_member.set(ID_component_name, name);
      lhs_member.copy_to_operands(lhs);

      exprt rhs_member;
    
      if(rhs.id()==ID_unknown ||
         rhs.id()==ID_invalid)
      {
        rhs_member=exprt(rhs.id(), subtype);
      }
      else
      {
        if (!base_type_eq(rhs.type(), type, ns))
        {
          std::cout << "RHS: " << rhs.type() << std::endl;
          std::cout << "LHS: " << type << std::endl;
        }
        
        assert(base_type_eq(rhs.type(), type, ns));
      
        if(rhs.id()==ID_struct ||
           rhs.id()==ID_constant)
        {
          assert(no<rhs.operands().size());
          rhs_member=rhs.operands()[no];
        }
        else if(rhs.id()==ID_with)
        {
          assert(rhs.operands().size()==3);

          // see if op1 is the member we want
          const exprt &member_operand=rhs.op1();

          const irep_idt &component_name=
            member_operand.get(ID_component_name);

          if(component_name==name)
          {
            // yes! just take op2
            rhs_member=rhs.op2();
          }
          else
          {
            // no! do op0
            rhs_member=exprt(ID_member, subtype);
            rhs_member.copy_to_operands(rhs.op0());
            rhs_member.set(ID_component_name, name);
          }
        }
        else
        {
          rhs_member=exprt(ID_member, subtype);
          rhs_member.copy_to_operands(rhs);
          rhs_member.set(ID_component_name, name);
        }

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
      assert(base_type_eq(rhs.type(), type, ns));
        
      if(rhs.id()==ID_array_of)
      {
        assert(rhs.operands().size()==1);
//        std::cout << "AOF: " << rhs.op0() << std::endl;
        assign(lhs_index, rhs.op0(), ns, add_to_sets);
      }
      else if(rhs.id()==ID_array ||
              rhs.id()==ID_constant)
      {
        forall_operands(o_it, rhs)
        {
          assign(lhs_index, *o_it, ns, add_to_sets);
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

Function: value_set_fivrnst::do_free

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_fivrnst::do_free(
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
  
  forall_objects(it, object_map)
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
    
    forall_valid_objects(o_it, old_object_map)
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
          insert_to(new_object_map, tmp, o);
          changed=true;
        }
      }
      else
        set(new_object_map, o_it);
    }
    
    if(changed)
    {
      entryt &temp_entry = get_temporary_entry(v_it->second.identifier,
                                               v_it->second.suffix);
      temp_entry.object_map=new_object_map;
    }
  }
}

/*******************************************************************\

Function: value_set_fivrnst::assign_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_fivrnst::assign_rec(
  const exprt &lhs,
  const object_mapt &values_rhs,
  const std::string &suffix,
  const namespacet &ns,
  bool add_to_sets)
{
  #if 0
  std::cout << "ASSIGN_REC LHS: " << lhs << std::endl;
  std::cout << "ASSIGN_REC SUFFIX: " << suffix << std::endl;

  for(object_map_dt::const_iterator it=values_rhs.read().begin(); 
      it!=values_rhs.read().end(); it++)
    std::cout << "ASSIGN_REC RHS: " << to_expr(it) << std::endl;
  #endif  

  if(lhs.id()==ID_symbol)
  {
    const irep_idt &identifier=lhs.get(ID_identifier);        

    if(has_prefix(id2string(identifier), 
                  "value_set::dynamic_object") ||
       has_prefix(id2string(identifier),
                  "value_set::return_value") ||
       values.find(id2string(identifier)+suffix)!=values.end())
       // otherwise we don't track this value 
    {
      entryt &temp_entry = get_temporary_entry(identifier, suffix);
      
      if(add_to_sets)
      {
        entryt &state_entry = get_entry(identifier, suffix);
        make_valid_union(temp_entry.object_map, state_entry.object_map);
      }
      
      make_union(temp_entry.object_map, values_rhs);
    }
  }
  else if(lhs.id()==ID_dynamic_object)
  {
    const dynamic_object_exprt &dynamic_object=
      to_dynamic_object_expr(lhs);
  
    const std::string name=
      "value_set::dynamic_object"+
      dynamic_object.instance().get_string(ID_value);

    entryt &temp_entry = get_temporary_entry(name, suffix);
    
    if(add_to_sets)
    {
      entryt &state_entry = get_entry(name, suffix);
      make_valid_union(temp_entry.object_map, state_entry.object_map);
    }
    
    make_union(temp_entry.object_map, values_rhs);
  }
  else if(lhs.id()==ID_dereference)
  {
    if(lhs.operands().size()!=1)
      throw lhs.id_string()+" expected to have one operand";
      
    object_mapt reference_set;
    get_reference_set(lhs, reference_set, ns);
      
    forall_objects(it, reference_set.read())
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

    assign_rec(lhs.op0(), values_rhs, "[]"+suffix, ns, add_to_sets);
  }
  else if(lhs.id()==ID_member)
  {
    if(lhs.operands().size()!=1)
      throw "member expected to have one operand";
    
    if(lhs.op0().is_nil()) return;
  
    const std::string &component_name=lhs.get_string(ID_component_name);

    const typet &type=ns.follow(lhs.op0().type());

    assert(type.id()==ID_struct ||
           type.id()==ID_union ||
           type.id()==ID_incomplete_struct ||
           type.id()==ID_incomplete_union);
           
    assign_rec(lhs.op0(), values_rhs, "."+component_name+suffix, 
               ns, add_to_sets);
  }
  else if(lhs.id()=="valid_object" ||
          lhs.id()=="dynamic_size" ||
          lhs.id()=="dynamic_type")
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
  
    assign_rec(typecast_expr.op(), values_rhs, suffix, 
               ns, add_to_sets);
  }
  else if(lhs.id()=="zero_string" ||
          lhs.id()=="is_zero_string" ||
          lhs.id()=="zero_string_length")
  {
    // ignore
  }
  else if(lhs.id()==ID_byte_extract_little_endian ||
          lhs.id()==ID_byte_extract_big_endian)
  {
    assert(lhs.operands().size()==2);
    assign_rec(lhs.op0(), values_rhs, suffix, ns, true);
  }
  else
    throw "assign NYI: `"+lhs.id_string()+"'";
}

/*******************************************************************\

Function: value_set_fivrnst::do_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_fivrnst::do_function_call(
  const irep_idt &function,
  const exprt::operandst &arguments,
  const namespacet &ns)
{
  const symbolt &symbol=ns.lookup(function);

  const code_typet &type=to_code_type(symbol.type);
  const code_typet::parameterst &parameter_types=type.parameters();

  // these first need to be assigned to dummy, temporary arguments
  // and only thereafter to the actuals, in order
  // to avoid overwriting actuals that are needed for recursive
  // calls

  // the assigned data must be valid on from!
  unsigned old_to_function=to_function;
  unsigned old_to_target_index=to_target_index;
  
  to_function=from_function;
  to_target_index=from_target_index;
  
  for(unsigned i=0; i<arguments.size(); i++)
  {
    const std::string identifier="value_set::" + id2string(function) + "::" +  
                                 "argument$"+i2string(i);
    add_var(identifier, "");
    exprt dummy_lhs=symbol_exprt(identifier, arguments[i].type());
//    std::cout << arguments[i] << std::endl;
    
    assign(dummy_lhs, arguments[i], ns, true);
    
    // merge it immediately, the actual assignment needs the data visible!
    // does this break the purpose of the dummies?
    make_union(values[identifier].object_map, 
               temporary_values[identifier].object_map);
  }
  
  // restore
  to_function=old_to_function;
  to_target_index=old_to_target_index;

  // now assign to 'actual actuals'

  unsigned i=0;

  for(code_typet::parameterst::const_iterator
      it=parameter_types.begin();
      it!=parameter_types.end();
      it++)
  {
    const irep_idt &identifier=it->get_identifier();
    if(identifier=="") continue;

    add_var(identifier, "");
  
    const exprt v_expr=
      symbol_exprt("value_set::" + id2string(function) + "::" + 
                   "argument$"+i2string(i), it->type());
    
    exprt actual_lhs=symbol_exprt(identifier, it->type());    
    assign(actual_lhs, v_expr, ns, true);
    i++;
  }
}

/*******************************************************************\

Function: value_set_fivrnst::do_end_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_fivrnst::do_end_function(
  const exprt &lhs,
  const namespacet &ns)
{
  if(lhs.is_nil()) return;

  irep_idt rvs = std::string("value_set::return_value") + 
                 i2string(from_function);
  add_var(rvs, "");
  symbol_exprt rhs(rvs, lhs.type());

  assign(lhs, rhs, ns);
}

/*******************************************************************\

Function: value_set_fivrnst::apply_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_fivrnst::apply_code(
  const exprt &code,
  const namespacet &ns)
{
  const irep_idt &statement=code.get(ID_statement);

  if(statement==ID_block)
  {
    forall_operands(it, code)
      apply_code(*it, ns);
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
    
    assign(lhs, exprt(ID_invalid, lhs.type()), ns);
  }
  else if(statement==ID_specc_notify ||
          statement==ID_specc_wait)
  {
    // ignore, does not change variables
  }
  else if(statement==ID_expression)
  {
    // can be ignored, we don't expect sideeffects here
  }
  else if(statement==ID_cpp_delete ||
          statement==ID_cpp_delete_array)
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
      irep_idt rvs = std::string("value_set::return_value") + 
                     i2string(from_function);
      add_var(rvs, "");      
      symbol_exprt lhs(rvs, code.op0().type());
      assign(lhs, code.op0(), ns);
    }
  }
  else
  {
    std::cerr << code.pretty() << std::endl;
    throw "value_set_fivrnst: unexpected statement: "+id2string(statement);
  }
}

/*******************************************************************\

Function: value_set_fivrnst::insert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_set_fivrnst::insert_to(
  object_mapt &dest, 
  unsigned n, 
  const objectt &object) const
{  
  object_map_dt &map = dest.write();
  if(map.find(n)==map.end())
  {
//    std::cout << "NEW(" << n << "): " << object_numbering[n] << std::endl;
    // new
    map[n]=object;      
    map.set_valid_at(n, to_function, to_target_index);    
    return true;
  }
  else
  {
//    std::cout << "UPD " << n << std::endl;
    objectt &old=map[n];
    
    bool res = map.set_valid_at(n, to_function, to_target_index);
    
    if(old.offset_is_set && object.offset_is_set)
    {
      if(old.offset==object.offset)
        return res;
      else
      {
        old.offset_is_set=false;
        return true;
      }
    }
    else if(!old.offset_is_set)
      return res;
    else
    {
      old.offset_is_set=false;
      return true;
    }
  }
}

/*******************************************************************\

Function: value_set_fivrnst::insert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_set_fivrnst::insert_from(
  object_mapt &dest, 
  unsigned n, 
  const objectt &object) const
{  
  object_map_dt &map = dest.write();
  if(map.find(n)==map.end())
  {
//    std::cout << "NEW(" << n << "): " << object_numbering[n] << std::endl;
    // new
    map[n]=object;      
    map.set_valid_at(n, from_function, from_target_index);    
    return true;
  }
  else
  {
//    std::cout << "UPD " << n << std::endl;
    objectt &old=map[n];
    
    bool res = map.set_valid_at(n, from_function, from_target_index);
    
    if(old.offset_is_set && object.offset_is_set)
    {
      if(old.offset==object.offset)
        return res;
      else
      {
        old.offset_is_set=false;
        return true;
      }
    }
    else if(!old.offset_is_set)
      return res;
    else
    {
      old.offset_is_set=false;
      return true;
    }
  }
}

/*******************************************************************\

Function: value_set_fivrnst::object_map_dt::set_valid_at

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_set_fivrnst::object_map_dt::set_valid_at(
  unsigned inx,
  unsigned f, 
  unsigned line)
{
  if(is_valid_at(inx, f, line)) return false;
  
  vrange_listt &ranges = validity_ranges[inx];  
  vrange_listt::iterator it=ranges.begin();
  
  while(it->function!=f && it!=ranges.end()) it++; // ffw to function block
  
  for(;
      it!=ranges.end() && it->function==f && it->from <= line;
      it++)
  {
    if(it->function==f)
    {
      if( line == it->to+1)
      {
        it->to++;
        
        // by any chance: does the next one connect to this one?
        vrange_listt::iterator n_it = it; n_it++;
        if(n_it!=ranges.end() &&
           it->function == n_it->function &&
           it->to+1 == n_it->from)
        {
          n_it->from = it->from; // connected!
          it = ranges.erase(it);
        }
        return true;
      }
    }
  }
  
  // it now points to either the end,
  // the first of a new function block,or
  // the first one that has from > line
  if(it!=ranges.end())
  {
    if(it->function==f)
    {
      if( line == it->from - 1)
      {
        it->from--;
        
        // by any chance: does the previous one connect to this one?
        if(it!=ranges.begin())
        {
          vrange_listt::iterator p_it = it; p_it--;
          if(p_it->function == it->function &&
             p_it->to+1 == it->from)
          {
            p_it->to = it->to; // connected!
            it = ranges.erase(it);
          }
        }
        return true;
      }
    }
  }
  
  // none matched
  validity_ranget insr(f, line, line);  
  ranges.insert(it, insr);
  
  return true;
}

/*******************************************************************\

Function: value_set_fivrnst::object_map_dt::is_valid_at

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_set_fivrnst::object_map_dt::is_valid_at(
  unsigned inx,
  unsigned f, 
  unsigned line) const
{
  #if 0
    std::cout << "IS_VALID_AT: " << inx << ", " << f << ", line " << line <<
      std::endl;
  #endif
  
  validity_rangest::const_iterator vrs = validity_ranges.find(inx);
  if(vrs!=validity_ranges.end())
  {    
    const vrange_listt &ranges = vrs->second;
    
    object_map_dt::vrange_listt::const_iterator it = ranges.begin();
    
    while(it->function!=f && 
          it!=ranges.end()) it++; // ffw to function block
    
    for(;
        it!=ranges.end() && it->function==f && it->from<=line ;
        it++)
      if(it->contains(f, line)) return true;
  }
  
  return false;
}

/*******************************************************************\

Function: value_set_fivrnst::handover

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_set_fivrnst::handover(void)
{
  bool changed=false;
  
  for (valuest::iterator it=values.begin();
       it!=values.end();
       it++)
  {
    object_mapt &state_map=it->second.object_map;

    irep_idt ident = id2string(it->second.identifier)+it->second.suffix;
    
    valuest::const_iterator t_it=temporary_values.find(ident);
    
    if(t_it==temporary_values.end())
    {
//      std::cout << "OLD VALUES FOR: " << ident << std::endl;
      Forall_valid_objects(o_it, state_map.write())
      {
//        std::cout << "STILL VALID: " << to_expr(o_it) << std::endl;
        if(state_map.write().set_valid_at(o_it->first, 
                                          to_function, to_target_index))
          changed = true;
      }
    }
    else
    {
//      std::cout << "NEW VALUES FOR: " << ident << std::endl;
      if(make_union(state_map, t_it->second.object_map))
        changed = true;
    }
  }
  
  temporary_values.clear();
  
  return changed;
}
