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
    return do_initializer_list(value, type, force_constant);
    
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
        tmp.type()=type;
      }
      else if(mp_integer(tmp.operands().size())<array_size)
      {
        // fill up
        tmp.type()=type;
        exprt zero=zero_initializer(full_type.subtype(), value.source_location(),
                                    *this, get_message_handler());
        tmp.operands().resize(integer2long(array_size), zero);
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
        tmp2.type()=type;
      }
      else if(mp_integer(tmp2.operands().size())<array_size)
      {
        // fill up
        tmp2.type()=type;
        exprt zero=zero_initializer(full_type.subtype(), value.source_location(),
                                    *this, get_message_handler());
        tmp2.operands().resize(integer2long(array_size), zero);
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
    if(symbol.is_macro)
    {
      // these must have a constant value
      assert(symbol.value.is_not_nil());
      typecheck_expr(symbol.value);
      source_locationt location=symbol.value.source_location();
      do_initializer(symbol.value, symbol.type, true);
      make_constant(symbol.value);
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
  entry.index=0;

  const typet &full_type=follow(type);
  
  if(full_type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(full_type);

    entry.size=struct_type.components().size();
    entry.subtype.make_nil();

    for(struct_typet::componentst::const_iterator
        it=struct_type.components().begin();
        it!=struct_type.components().end();
        ++it)
    {
      if(it->type().id()!=ID_code &&
         !it->get_is_padding())
      {
        entry.subtype=it->type();
        break;
      }

      ++entry.index;
    }
  }
  else if(full_type.id()==ID_union)
  {
    const union_typet &union_type=to_union_type(full_type);

    if(union_type.components().empty())
    {
      entry.size=0;
      entry.subtype.make_nil();
    }
    else
    {
      // The default is to unitialize using the first member of the
      // union.
      entry.size=1;
      entry.subtype=union_type.components().front().type();
    }
  }
  else if(full_type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(full_type);

    if(array_type.size().is_nil())
    {
      entry.size=0;
      entry.subtype=array_type.subtype();
    }
    else
    {
      mp_integer array_size;

      if(to_integer(array_type.size(), array_size))
      {
        err_location(array_type.size());
        str << "array has non-constant size `"
            << to_string(array_type.size()) << "'";
        throw 0;
      }

      entry.size=integer2long(array_size);
      entry.subtype=array_type.subtype();
    }
  }
  else if(full_type.id()==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(full_type);

    mp_integer vector_size;

    if(to_integer(vector_type.size(), vector_size))
    {
      err_location(vector_type.size());
      str << "vector has non-constant size `"
          << to_string(vector_type.size()) << "'";
      throw 0;
    }

    entry.size=integer2long(vector_size);
    entry.subtype=vector_type.subtype();
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

  for(size_t i=0; i<designator.size(); i++)
  {
    size_t index=designator[i].index;
    const typet &type=designator[i].type;
    const typet &full_type=follow(type);

    if(full_type.id()==ID_array ||
       full_type.id()==ID_vector)
    {
      if(index>=dest->operands().size())
      {
        if(full_type.id()==ID_array &&
           (to_array_type(full_type).size().is_zero() ||
            to_array_type(full_type).size().is_nil()))
        {
          // we are willing to grow an incomplete or zero-sized array
          exprt zero=zero_initializer(full_type.subtype(), value.source_location(), *this, get_message_handler());
          dest->operands().resize(integer2long(index)+1, zero);
          
          // todo: adjust type!
        }
        else
        {
          err_location(value);
          str << "array index designator " << index
              << " out of bounds (" << dest->operands().size() << ")";
          throw 0;
        }
      }

      dest=&(dest->operands()[integer2long(index)]);
    }
    else if(full_type.id()==ID_struct)
    {
      const struct_typet::componentst &components=
        to_struct_type(full_type).components();

      if(index>=dest->operands().size())
      {
        err_location(value);
        str << "structure member designator " << index
            << " out of bounds (" << dest->operands().size() << ")";
        throw 0;
      }

      assert(index<components.size());
      assert(components[index].type().id()!=ID_code &&
             !components[index].get_is_padding());

      dest=&(dest->operands()[index]);
    }
    else if(full_type.id()==ID_union)
    {
      const union_typet &union_type=to_union_type(full_type);

      const union_typet::componentst &components=
        union_type.components();

      assert(index<components.size());

      const union_typet::componentt &component=union_type.components()[index];

      if(dest->id()==ID_union &&
         dest->get(ID_component_name)==component.get_name())
      {
        // Already right union component. We can initialize multiple submembers,
        // so do not overwrite this.
      }
      else
      {
        // Note that gcc issues a warning if the union component is switched.
        // Build a union expression from given component.
        union_exprt union_expr(type);
        union_expr.op()=zero_initializer(component.type(), value.source_location(), *this, get_message_handler());
        union_expr.add_source_location()=value.source_location();
        union_expr.set_component_name(component.get_name());
        *dest=union_expr;
      }

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

    const typet &type=designator.back().subtype;
    const typet &full_type=follow(type);
    assert(full_type.id()!=ID_symbol);

    // do we initialize a scalar?
    if(full_type.id()!=ID_struct &&
       full_type.id()!=ID_union &&
       full_type.id()!=ID_array &&
       full_type.id()!=ID_vector)
    {
      // The initializer for a scalar shall be a single expression,
      // * optionally enclosed in braces. *
      
      if(value.id()==ID_initializer_list &&
         value.operands().size()==1)
        *dest=do_initializer_rec(value.op0(), type, force_constant);
      else
        *dest=do_initializer_rec(value, type, force_constant);

      assert(full_type==follow(dest->type()));
      
      return; // done
    }
    
    // union? The component in the zero initializer might
    // not be the first one.
    if(full_type.id()==ID_union)
    {
      const union_typet &union_type=to_union_type(full_type);

      const union_typet::componentst &components=
        union_type.components();

      if(!components.empty())
      {
        const union_typet::componentt &component=union_type.components().front();

        union_exprt union_expr(type);
        union_expr.op()=zero_initializer(component.type(), value.source_location(), *this, get_message_handler());
        union_expr.add_source_location()=value.source_location();
        union_expr.set_component_name(component.get_name());
        *dest=union_expr;
      }
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
      if(full_type.id()==ID_array &&
         (follow(full_type.subtype()).id()==ID_signedbv ||
          follow(full_type.subtype()).id()==ID_unsignedbv))
      {
        *dest=do_initializer_rec(value, type, force_constant);
        return; // done
      }
    }
    else if(follow(value.type())==full_type)
    {
      // a struct/union/vector can be initialized directly with
      // an expression of the right type. This doesn't
      // work with arrays, unfortunately.
      if(full_type.id()==ID_struct ||
         full_type.id()==ID_union ||
         full_type.id()==ID_vector)
      {
        *dest=value;
        return; // done
      }
    }

    assert(full_type.id()==ID_struct ||
           full_type.id()==ID_union ||
           full_type.id()==ID_array ||
           full_type.id()==ID_vector);
    
    // we are initializing a compound type, and enter it!
    // this may change the type, full_type might not be valid anymore
    const typet dest_type=full_type;
    designator_enter(type, designator);
    
    if(dest->operands().empty())
    {
      err_location(value);
      str << "cannot initialize type `"
          << to_string(dest_type) << "' using value `"
          << to_string(value) << "'";
      throw 0;
    }

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
    const typet &full_type=follow(entry.type);

    entry.index++;
    
    if(full_type.id()==ID_array &&
       to_array_type(full_type).size().is_nil())
      return; // we will keep going forever

    if(full_type.id()==ID_struct &&
       entry.index<entry.size)
    {
      // need to adjust subtype
      const struct_typet &struct_type=
        to_struct_type(full_type);
      const struct_typet::componentst &components=
        struct_type.components();
      assert(components.size()==entry.size);
      
      // we skip over any padding or code
      while(entry.index<entry.size &&
            (components[entry.index].get_is_padding() ||
             components[entry.index].type().id()==ID_code))
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

  typet type=src_type;
  designatort designator;
  
  forall_operands(it, src)
  {
    const exprt &d_op=*it;
    designatort::entryt entry;
    entry.type=type;
    const typet &full_type=follow(entry.type);

    if(full_type.id()==ID_array)
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

      if(to_array_type(full_type).size().is_nil())
        size=0;
      else if(to_integer(to_array_type(full_type).size(), size))
      {
        err_location(d_op.op0());
        throw "expected constant array size";
      }
      
      entry.index=integer2long(index);
      entry.size=integer2long(size);
      entry.subtype=full_type.subtype();
    }
    else if(full_type.id()==ID_struct ||
            full_type.id()==ID_union)
    {
      const struct_union_typet &struct_union_type=to_struct_union_type(full_type);
    
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
        entry.subtype=struct_union_type.components()[entry.index].type();
      }
      else
      {
        // We will search for anonymous members,
        // in a loop. This isn't supported by gcc, but icc does allow it.
        
        bool found=false, repeat;
        typet tmp_type=entry.type;
        
        do
        {
          repeat=false;
          unsigned number=0;        
          const struct_union_typet::componentst &components=
            to_struct_union_type(follow(tmp_type)).components();

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
              entry.subtype=components[entry.index].type();
              entry.type=tmp_type;
            }
            else if(c_it->get_anonymous() &&
                    (follow(c_it->type()).id()==ID_struct ||
                     follow(c_it->type()).id()==ID_union) &&
                    has_component_rec(
                      c_it->type(), component_name, *this))
            {
              entry.index=number;
              entry.size=components.size();
              entry.subtype=c_it->type();
              entry.type=tmp_type;
              tmp_type=entry.subtype;
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
          << to_string(full_type) << "'";
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

  const typet &full_type=follow(type);

  exprt result;
  if(full_type.id()==ID_struct ||
     full_type.id()==ID_union ||
     full_type.id()==ID_vector)
  {
    // start with zero everywhere
    result=zero_initializer(type, value.source_location(), *this, get_message_handler());
  }
  else if(full_type.id()==ID_array)
  {
    if(to_array_type(full_type).size().is_nil())
    {
      // start with empty array
      result=exprt(ID_array, full_type);
      result.add_source_location()=value.source_location();
    }
    else
    {
      // start with zero everywhere
      result=zero_initializer(type, value.source_location(), *this, get_message_handler());
    }

    // 6.7.9, 14: An array of character type may be initialized by a character
    // string literal or UTF-8 string literal, optionally enclosed in braces.
    if(value.operands().size()>=1 &&
       value.op0().id()==ID_string_constant &&
       (full_type.subtype().id()==ID_signedbv ||
        full_type.subtype().id()==ID_unsignedbv) &&
       full_type.subtype().get(ID_width)==char_type().get(ID_width))
    {
      if(value.operands().size()>1)
      {
        err_location(value);
        warning("ignoring excess initializers");
      }

      return do_initializer_rec(value.op0(), type, force_constant);
    }
  }
  else
  {
    // The initializer for a scalar shall be a single expression,
    // * optionally enclosed in braces. *

    if(value.operands().size()==1)
      return do_initializer_rec(value.op0(), type, force_constant);
    
    err_location(value);
    str << "cannot initialize `" << to_string(full_type)
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

  // make sure we didn't mess up index computation
  if(full_type.id()==ID_struct)
  {
    assert(result.operands().size()==
           to_struct_type(full_type).components().size());
  }
  
  if(full_type.id()==ID_array &&
     to_array_type(full_type).size().is_nil())
  {
    // make complete by setting array size
    size_t size=result.operands().size();
    result.type().id(ID_array);
    result.type().set(ID_size, from_integer(size, index_type()));
  }
  
  return result;
}
