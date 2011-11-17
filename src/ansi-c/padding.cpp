/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <config.h>
#include <i2string.h>
#include <pointer_offset_size.h>

#include "padding.h"

/*******************************************************************\

Function: alignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned alignment(const typet &type, const namespacet &ns)
{
  if(type.id()==ID_array)
  {
    return alignment(type.subtype(), ns);
  }
  else if(type.id()==ID_struct || type.id()==ID_union)
  {
    const struct_union_typet::componentst &components=
      to_struct_union_type(type).components();

    unsigned result=1;

    // get the max
    // (should really be the smallest common denominator)
    for(struct_union_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
      result=std::max(result, alignment(it->type(), ns));

    return result;
  }
  else if(type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_floatbv)
  {
    unsigned width=type.get_int(ID_width);
    return width%8?width/8+1:width/8;
  }
  else if(type.id()==ID_pointer)
  {
    unsigned width=config.ansi_c.pointer_width;
    return width%8?width/8+1:width/8;
  }
  else if(type.id()==ID_symbol)
    return alignment(ns.follow(type), ns);

  return 1;
}

/*******************************************************************\

Function: add_padding

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void add_padding(struct_typet &type, const namespacet &ns)
{
  struct_typet::componentst &components=type.components();

  // first do padding for bit-fields

  {  
    unsigned padding_counter=0;
    unsigned bit_field_bits=0;

    for(struct_typet::componentst::iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      if(it->get_is_bit_field())
      {
        // count the bits
        bit_field_bits+=it->type().get_int(ID_width);
      }
      else if(bit_field_bits!=0)
      {
        // not on a byte-boundary?
        if((bit_field_bits%8)!=0)
        {
          unsigned pad=8-bit_field_bits%8;
          unsignedbv_typet padding_type;
          padding_type.set_width(pad);
          
          struct_typet::componentt component;
          component.type()=padding_type;
          component.set_name("$bit_field_pad"+i2string(padding_counter++));
          component.set_is_padding(true);
          component.set_is_bit_field(true);
          
          it=components.insert(it, component);
          it++; // skip over
        
          bit_field_bits+=pad;
        }

        bit_field_bits=0;
      }
    }

    // Add padding at the end?
    if((bit_field_bits%8)!=0)
    {
      unsigned pad=8-bit_field_bits%8;
      unsignedbv_typet padding_type;
      padding_type.set_width(pad);
      
      struct_typet::componentt component;
      component.type()=padding_type;
      component.set_name("$bit_field_pad"+i2string(padding_counter++));
      component.set_is_padding(true);
      component.set_is_bit_field(true);
      
      components.push_back(component);
    }  
  }

  // packed?
  if(type.get_bool(ID_packed))
    return; // done

  mp_integer offset=0;
  unsigned padding_counter=0;
  unsigned max_alignment=0;
  unsigned bit_field_bits=0;

  for(struct_typet::componentst::iterator
      it=components.begin();
      it!=components.end();
      it++)
  {
    // ANSI-C says that bit-fields do not get padded!
    if(it->get_is_bit_field())
    {
      // count the bits
      bit_field_bits+=it->type().get_int(ID_width);
    
      // we consider the type for max_alignment, however
      unsigned a=alignment(it->get_bit_field_type(), ns);
      if(max_alignment<a) 
        max_alignment=a;
      continue;
    }
    else if(bit_field_bits!=0)
    {
      // these are now assumed to be multiples of 8
      offset+=bit_field_bits/8;
      bit_field_bits=0;
    }
    
    const typet &it_type=it->type();
    unsigned a=alignment(it_type, ns);
    
    // check minimum alignment
    if(a<config.ansi_c.alignment)
      a=config.ansi_c.alignment;
      
    if(max_alignment<a) 
      max_alignment=a;
  
    if(a!=1)
    {
      // we may need to align it
      unsigned displacement=integer2long(offset%a);

      if(displacement!=0)
      {
        unsigned pad=a-displacement;
      
        unsignedbv_typet padding_type;
        padding_type.set_width(pad*8);
        
        struct_typet::componentt component;
        component.type()=padding_type;
        component.set_name("$pad"+i2string(padding_counter++));
        component.set_is_padding(true);
        
        it=components.insert(it, component);
        it++; // skip over
        
        offset+=pad;
      }
    }
    
    mp_integer size=pointer_offset_size(ns, it_type);
    
    if(size!=-1)
      offset+=size;
  }
  
  if(bit_field_bits!=0)
  {
    // these are now assumed to be multiples of 8
    offset+=bit_field_bits/8;
  }

  // There may be a need for 'end of struct' padding.
  // We use 'max_alignment'.

  if(max_alignment>1)
  {
    // we may need to align it
    unsigned displacement=integer2long(offset%max_alignment);

    if(displacement!=0)
    {
      unsigned pad=max_alignment-displacement;
    
      unsignedbv_typet padding_type;
      padding_type.set_width(pad*8);

      struct_typet::componentst::iterator it;
      
      // we need to insert before any 'flexible member'
      if(!components.empty() &&
         components.back().type().id()==ID_array &&
         to_array_type(components.back().type()).size().is_zero())
      {
        it=components.end();
        it--;
      }
      else
        it=components.end();

      struct_typet::componentt component;
      component.type()=padding_type;
      component.set_name("$pad"+i2string(padding_counter++));
      component.set_is_padding(true);
      
      components.insert(it, component);
    }
  }
}
