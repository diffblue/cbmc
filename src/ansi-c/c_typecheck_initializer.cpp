/*******************************************************************\

Module: ANSI-C Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/config.h>
#include <util/type_eq.h>
#include <util/std_types.h>
#include <util/expr_util.h>
#include <util/simplify_expr.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>
#include <util/std_types.h>

#include <linking/zero_initializer.h>

#include "c_types.h"
#include "c_typecheck_base.h"
#include "string_constant.h"
#include "anonymous_member.h"

/*******************************************************************\

Function: c_typecheck_baset::do_initializer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::do_initializer(
  exprt &initializer,
  const typet &type,
  bool force_constant)
{
  exprt result=do_initializer_rec(initializer, type, force_constant);

  if(type.id()==ID_array)
  {
    // any arrays must have a size
    const typet &result_type=follow(result.type());
    assert(result_type.id()==ID_array &&
           to_array_type(result_type).size().is_not_nil());
           
    // we don't allow initialisation with symbols of array type
    if(result.id()!=ID_array)
    {
      err_location(result);
      throw "invalid array initializer";
    }
  }
    
  initializer=result;
}

/*******************************************************************\

Function: c_typecheck_baset::do_initializer_rec

  Inputs:

 Outputs:

 Purpose: initialize something of type `type' with given
          value `value'

\*******************************************************************/

exprt c_typecheck_baset::do_initializer_rec(
  const exprt &value,
  const typet &type,
  bool force_constant)
{
  const typet &full_type=follow(type);
  
  if(full_type.id()==ID_incomplete_struct)
  {
    err_location(value);
    str << "type `"
        << to_string(full_type) << "' is still incomplete -- cannot initialize";
    throw 0;
  }
  
  if(value.id()==ID_initializer_list)
    return do_initializer_list(value, full_type, force_constant);
    
  if(value.id()==ID_array &&
     value.get_bool(ID_C_string_constant) &&
     full_type.id()==ID_array &&
     (full_type.subtype().id()==ID_signedbv ||
      full_type.subtype().id()==ID_unsignedbv) &&
      full_type.subtype().get(ID_width)==value.type().subtype().get(ID_width))
  {
    exprt tmp=value;

    // adjust char type
    tmp.type().subtype()=full_type.subtype();
    
    Forall_operands(it, tmp)
      it->type()=full_type.subtype();

    if(full_type.id()==ID_array &&
       to_array_type(full_type).is_complete())
    {
      // check size
      mp_integer array_size;
      if(to_integer(to_array_type(full_type).size(), array_size))
      {
        err_location(value);
        throw "array size needs to be constant";
      }
      
      if(array_size<0)
      {
        err_location(value);
        throw "array size must not be negative";
      }

      if(mp_integer(tmp.operands().size())>array_size)
      {
        // cut off long strings. gcc does a warning for this
        tmp.operands().resize(integer2long(array_size));
        tmp.type()=full_type;
      }
      else if(mp_integer(tmp.operands().size())<array_size)
      {
        // fill up
        tmp.type()=full_type;
        tmp.operands().resize(integer2long(array_size),
          gen_zero(full_type.subtype()));
      }
    }
    
    return tmp;
  }
  
  if(value.id()==ID_string_constant &&
     full_type.id()==ID_array &&
     (full_type.subtype().id()==ID_signedbv ||
      full_type.subtype().id()==ID_unsignedbv) &&
      full_type.subtype().get(ID_width)==char_type().get(ID_width))
  {
    // will go away, to be replaced by the above block
  
    string_constantt tmp1=to_string_constant(value);
    // adjust char type
    tmp1.type().subtype()=full_type.subtype();

    exprt tmp2=tmp1.to_array_expr();

    if(full_type.id()==ID_array &&
       to_array_type(full_type).is_complete())
    {
      // check size
      mp_integer array_size;
      if(to_integer(to_array_type(full_type).size(), array_size))
      {
        err_location(value);
        throw "array size needs to be constant";
      }
      
      if(array_size<0)
      {
        err_location(value);
        throw "array size must not be negative";
      }

      if(mp_integer(tmp2.operands().size())>array_size)
      {
        // cut off long strings. gcc does a warning for this
        tmp2.operands().resize(integer2long(array_size));
        tmp2.type()=full_type;
      }
      else if(mp_integer(tmp2.operands().size())<array_size)
      {
        // fill up
        tmp2.type()=full_type;
        tmp2.operands().resize(integer2long(array_size),
          gen_zero(full_type.subtype()));
      }
    }
    
    return tmp2;
  }
  
  if(full_type.id()==ID_array &&
     to_array_type(full_type).size().is_nil())
  {
    err_location(value);
    str << "type `"
        << to_string(full_type) << "' cannot be initialized with `"
        << to_string(value) << "'";
    throw 0;
  }

  if(value.id()==ID_designated_initializer)
  {
    err_location(value);
    str << "type `"
        << to_string(full_type)
        << "' cannot be initialized with designated initializer";
    throw 0;
  }

  exprt result=value;
  implicit_typecast(result, type);
  return result;
}

/*******************************************************************\

Function: c_typecheck_baset::do_initializer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::do_initializer(symbolt &symbol)
{
  // this one doesn't need initialization
  if(has_prefix(id2string(symbol.name), CPROVER_PREFIX "constant_infinity"))
    return;

  if(symbol.is_static_lifetime)
  {
    if(symbol.value.is_not_nil())
    {
      typecheck_expr(symbol.value);
      do_initializer(symbol.value, symbol.type, true);

      // need to adjust size?
      if(follow(symbol.type).id()==ID_array &&
         to_array_type(follow(symbol.type)).size().is_nil())
        symbol.type=symbol.value.type();
    }
  }
  else if(!symbol.is_type)
  {
    const typet &final_type=follow(symbol.type);
    
    if(final_type.id()==ID_incomplete_c_enum ||
       final_type.id()==ID_c_enum)
    {
      if(symbol.is_macro)
      {
        // these must have a constant value
        assert(symbol.value.is_not_nil());
        typecheck_expr(symbol.value);
        locationt location=symbol.value.location();
        do_initializer(symbol.value, symbol.type, true);
        make_constant(symbol.value);
      }
      else
      {
        if(symbol.value.is_not_nil())
          typecheck_expr(symbol.value);
      }
    }
    else if(symbol.value.is_not_nil())
    {
      typecheck_expr(symbol.value);
      do_initializer(symbol.value, symbol.type, true);
      
      // need to adjust size?
      if(follow(symbol.type).id()==ID_array &&
         to_array_type(follow(symbol.type)).size().is_nil())
        symbol.type=symbol.value.type();
    }
  }
}

/*******************************************************************\

Function: c_typecheck_baset::designator_enter

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::designator_enter(
  const typet &type,
  designatort &designator)
{
  designatort::entryt entry;
  entry.type=type;

  assert(entry.type.id()!=ID_symbol);
  
  if(entry.type.id()==ID_struct)
  {
    entry.size=to_struct_type(entry.type).components().size();

    if(entry.size!=0)
      entry.subtype=to_struct_type(entry.type).components().front().type();
    else
      entry.subtype.make_nil();
  }
  else if(entry.type.id()==ID_union)
  {
    if(to_union_type(entry.type).components().empty())
    {
      entry.size=0;
      entry.subtype.make_nil();
    }
    else
    {
      entry.size=1;
      entry.subtype=to_union_type(entry.type).components().front().type();
    }
  }
  else if(entry.type.id()==ID_array)
  {
    if(to_array_type(entry.type).size().is_nil())
    {
      entry.size=0;
      entry.subtype=entry.type.subtype();
    }
    else
    {
      mp_integer array_size;

      if(to_integer(to_array_type(entry.type).size(), array_size))
      {
        err_location(to_array_type(entry.type).size());
        str << "array has non-constant size `"
            << to_string(to_array_type(entry.type).size()) << "'";
        throw 0;
      }

      entry.size=integer2long(array_size);
      entry.subtype=entry.type.subtype();
    }
  }
  else if(entry.type.id()==ID_vector)
  {
    mp_integer vector_size;

    if(to_integer(to_vector_type(entry.type).size(), vector_size))
    {
      err_location(to_vector_type(entry.type).size());
      str << "vector has non-constant size `"
          << to_string(to_vector_type(entry.type).size()) << "'";
      throw 0;
    }

    entry.size=integer2long(vector_size);
    entry.subtype=entry.type.subtype();
  }
  else
    assert(false);

  designator.push_entry(entry);
}

/*******************************************************************\

Function: c_typecheck_baset::do_designated_initializer

  Inputs: pre-initialized result, designator

 Outputs: sets result

 Purpose:

\*******************************************************************/

void c_typecheck_baset::do_designated_initializer(
  exprt &result,
  designatort &designator,
  const exprt &value,
  bool force_constant)
{
  assert(!designator.empty());
  
  if(value.id()==ID_designated_initializer)
  {
    assert(value.operands().size()==1);

    designator=    
      make_designator(
        designator.front().type,
        static_cast<const exprt &>(value.find(ID_designator)));
        
    assert(!designator.empty());
  
    return do_designated_initializer(
      result, designator, value.op0(), force_constant);
  }
  
  exprt *dest=&result;

  // first phase: follow given designator

  for(unsigned i=0; i<designator.size(); i++)
  {
    unsigned index=designator[i].index;
    const typet &type=designator[i].type;
    
    assert(type.id()!=ID_symbol);

    if(type.id()==ID_array ||
       type.id()==ID_vector ||
       type.id()==ID_struct)
    {
      if(index>=dest->operands().size())
      {
        if(type.id()==ID_array && 
           (to_array_type(type).size().is_zero() ||
            to_array_type(type).size().is_nil()))
        {
          // we are willing to grow an incomplete or zero-sized array
          exprt zero=zero_initializer(type.subtype(), value.location(), *this, get_message_handler());
          dest->operands().resize(integer2long(index)+1, zero);
          
          // todo: adjust type!
        }
        else
        {
          err_location(value);
          str << "index designator " << index
              << " out of bounds (" << dest->operands().size() << ")";
          throw 0;
        }
      }

      dest=&(dest->operands()[integer2long(index)]);
    }
    else if(type.id()==ID_union)
    {
      // union initialization is quite special
      const union_typet &union_type=to_union_type(type);
      const union_typet::componentt &component=union_type.components()[index];

      // build a union expression from the argument
      exprt union_expr(ID_union, type);
      union_expr.operands().resize(1);
      union_expr.op0()=zero_initializer(component.type(), value.location(), *this, get_message_handler());
      union_expr.location()=value.location();
      union_expr.set(ID_component_name, component.get_name());

      *dest=union_expr;
      dest=&(dest->op0());
    }
    else
      assert(false);
  }
  
  // second phase: assign value
  // for this, we may need to go down, adding to the designator
  
  while(true)
  {
    // see what type we have to initialize

    typet type=follow(designator.back().subtype);
    assert(type.id()!=ID_symbol);

    // do we initialize a scalar?
    if(type.id()!=ID_struct &&
       type.id()!=ID_union &&
       type.id()!=ID_array &&
       type.id()!=ID_vector)
    {
      // The initializer for a scalar shall be a single expression,
      // * optionally enclosed in braces. *
      
      if(value.id()==ID_initializer_list &&
         value.operands().size()==1)
        *dest=do_initializer_rec(value.op0(), type, force_constant);
      else
        *dest=do_initializer_rec(value, type, force_constant);

      assert(type==follow(dest->type()));
      
      return; // done
    }

    // see what initializer we are given
    if(value.id()==ID_initializer_list)
    {
      *dest=do_initializer_rec(value, type, force_constant);
      return; // done
    }
    else if(value.id()==ID_string_constant)
    {
      // We stop for initializers that are string-constants,
      // which are like arrays. We only do so if we are to
      // initialize an array of scalars.
      if(type.id()==ID_array &&
         (follow(type.subtype()).id()==ID_signedbv ||
          follow(type.subtype()).id()==ID_unsignedbv))
      {
        *dest=do_initializer_rec(value, type, force_constant);
        return; // done
      }
    }
    else if(follow(value.type())==type)
    {
      // a struct/union/vector can be initialized directly with
      // an expression of the right type. This doesn't
      // work with arrays, unfortunately.
      if(type.id()==ID_struct || type.id()==ID_union || type.id()==ID_vector)
      {
        *dest=value;
        return; // done
      }
    }

    assert(type.id()==ID_struct ||
           type.id()==ID_union ||
           type.id()==ID_array ||
           type.id()==ID_vector);
    
    // we are initializing a compound type, and enter it!
    designator_enter(type, designator);
    
    assert(!dest->operands().empty());
    dest=&(dest->op0());

    // we run into another loop iteration
  }
}

/*******************************************************************\

Function: c_typecheck_baset::increment_designator

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::increment_designator(designatort &designator)
{
  assert(!designator.empty());

  while(true)
  {
    designatort::entryt &entry=designator[designator.size()-1];

    entry.index++;
    
    if(entry.type.id()==ID_array &&
       to_array_type(entry.type).size().is_nil())
      return; // we will keep going forever

    if(entry.type.id()==ID_struct &&
       entry.index<entry.size)
    {
      // need to adjust subtype
      const struct_typet &struct_type=
        to_struct_type(entry.type);
      const struct_typet::componentst &components=
        struct_type.components();
      assert(components.size()==entry.size);
      
      // we skip over any padding
      while(entry.index<entry.size &&
            components[entry.index].get_is_padding())
        entry.index++;

      if(entry.index<entry.size)
        entry.subtype=components[entry.index].type();
    }

    if(entry.index<entry.size) return; // done
    
    if(designator.size()==1) return; // done
    
    // pop entry
    designator.pop_entry();
    
    assert(!designator.empty());
  }
}

/*******************************************************************\

Function: c_typecheck_baset::make_designator

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

designatort c_typecheck_baset::make_designator(
  const typet &src_type,
  const exprt &src)
{
  assert(!src.operands().empty());

  typet type=follow(src_type);
  designatort designator;
  
  forall_operands(it, src)
  {
    const exprt &d_op=*it;
    designatort::entryt entry;
    entry.type=type;

    assert(type.id()!=ID_symbol);

    if(type.id()==ID_array)
    {
      if(d_op.id()!=ID_index)
      {
        err_location(d_op);
        throw "expected array index designator";
      }

      assert(d_op.operands().size()==1);
      exprt tmp_index=d_op.op0();
      make_constant_index(tmp_index);

      mp_integer index, size;

      if(to_integer(tmp_index, index))
      {
        err_location(d_op.op0());
        throw "expected constant array index designator";
      }

      if(to_array_type(type).size().is_nil())
        size=0;
      else if(to_integer(to_array_type(type).size(), size))
      {
        err_location(d_op.op0());
        throw "expected constant array size";
      }
      
      entry.index=integer2long(index);
      entry.size=integer2long(size);
      entry.subtype=follow(type.subtype());
    }
    else if(type.id()==ID_struct || type.id()==ID_union)
    {
      const struct_union_typet &struct_union_type=to_struct_union_type(type);
    
      if(d_op.id()!=ID_member)
      {
        err_location(d_op);
        throw "expected member designator";
      }

      const irep_idt &component_name=d_op.get(ID_component_name);

      if(struct_union_type.has_component(component_name))
      {
        // a direct member
        entry.index=struct_union_type.component_number(component_name);
        entry.size=struct_union_type.components().size();
        entry.subtype=follow(struct_union_type.components()[entry.index].type());
      }
      else
      {
        // We will search for anonymous members,
        // in a loop. This isn't supported by gcc, but icc does allow it.
        
        bool found=false, repeat;
        struct_union_typet tmp_type=struct_union_type;
        
        do
        {
          repeat=false;
          unsigned number=0;        
          const struct_union_typet::componentst &components=
            tmp_type.components();

          for(struct_union_typet::componentst::const_iterator
              c_it=components.begin();
              c_it!=components.end();
              c_it++, number++)
          {
            if(c_it->get_name()==component_name)
            {
              // done!
              entry.index=number;
              entry.size=components.size();
              entry.subtype=follow(components[entry.index].type());
              entry.type=tmp_type;
            }
            else if(c_it->get_anonymous() &&
                    has_component_rec(
                      c_it->type(), component_name, *this))
            {
              entry.index=number;
              entry.size=components.size();
              entry.subtype=follow(c_it->type());
              entry.type=tmp_type;
              tmp_type=to_struct_union_type(entry.subtype);
              designator.push_entry(entry);
              found=repeat=true;
              break;
            }
          }
        }
        while(repeat);
      
        if(!found)
        {
          err_location(d_op);
          str << "failed to find struct component `" << component_name 
              << "' in initialization of `" << to_string(struct_union_type) << "'";
          throw 0;
        }
      }
    }
    else
    {
      err_location(d_op);
      str << "designated initializers cannot initialize `"
          << to_string(type) << "'";
      throw 0;
    }

    type=entry.subtype;    
    designator.push_entry(entry);
  }
  
  assert(!designator.empty());
  
  return designator;
}

/*******************************************************************\

Function: c_typecheck_baset::do_initializer_list

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt c_typecheck_baset::do_initializer_list(
  const exprt &value,
  const typet &type,
  bool force_constant)
{
  assert(value.id()==ID_initializer_list);

  if(type.id()==ID_symbol)
    return do_initializer_list(
      value, follow(type), force_constant);

  exprt result;
  if(type.id()==ID_struct ||
     type.id()==ID_union)
  {
    // start with zero everywhere
    result=zero_initializer(type, value.location(), *this, get_message_handler());
  }
  else if(type.id()==ID_array)
  {
    if(to_array_type(type).size().is_nil())
    {
      // start with empty array
      result=exprt(ID_array, type);
      result.location()=value.location();
    }
    else
    {
      // start with zero everywhere
      result=zero_initializer(type, value.location(), *this, get_message_handler());
    }
  }
  else if(type.id()==ID_vector)
  {
    // start with zero everywhere
    result=zero_initializer(type, value.location(), *this, get_message_handler());
  }
  else
  {
    // The initializer for a scalar shall be a single expression,
    // * optionally enclosed in braces. *

    if(value.operands().size()==1)
      return do_initializer_rec(value.op0(), type, force_constant);
    
    err_location(value);
    str << "cannot initialize `" << to_string(type)
        << "' with an initializer list";
    throw 0;
  }

  designatort current_designator;
  
  designator_enter(type, current_designator);

  forall_operands(it, value)
  {
    do_designated_initializer(
      result, current_designator, *it, force_constant);

    // increase designator -- might go up    
    increment_designator(current_designator);
  }
  
  if(type.id()==ID_array &&
     to_array_type(type).size().is_nil())
  {
    // make complete by setting array size
    unsigned size=result.operands().size();
    result.type().id(ID_array);
    result.type().set(ID_size, from_integer(size, index_type()));
  }
  
  return result;
}
