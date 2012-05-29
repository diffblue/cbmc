/*******************************************************************\

Module: SpecC Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <iostream>

#include <config.h>
#include <arith_tools.h>
#include <std_types.h>

#include "ansi_c_convert_type.h"

/*******************************************************************\

Function: ansi_c_convert_typet::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_convert_typet::read(const typet &type)
{
  clear();
  location=type.location();
  read_rec(type);
}

/*******************************************************************\

Function: ansi_c_convert_typet::read_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_convert_typet::read_rec(const typet &type)
{
  if(type.id()==ID_merged_type)
  {
    forall_subtypes(it, type)
      read_rec(*it);
  }
  else if(type.id()==ID_signed)
    signed_cnt++;
  else if(type.id()==ID_unsigned)
    unsigned_cnt++;
  else if(type.id()==ID_ptr32)
    c_qualifiers.is_ptr32=true;
  else if(type.id()==ID_ptr64)
    c_qualifiers.is_ptr64=true;
  else if(type.id()==ID_volatile)
    c_qualifiers.is_volatile=true;
  else if(type.id()==ID_asm)
  {
    // ignore for now
  }
  else if(type.id()==ID_const)
    c_qualifiers.is_constant=true;
  else if(type.id()==ID_restricted)
    c_qualifiers.is_restricted=true;
  else if(type.id()==ID_char)
    char_cnt++;
  else if(type.id()==ID_int)
    int_cnt++;
  else if(type.id()==ID_int8)
    int8_cnt++;
  else if(type.id()==ID_int16)
    int16_cnt++;
  else if(type.id()==ID_int32)
    int32_cnt++;
  else if(type.id()==ID_int64)
    int64_cnt++;
  else if(type.id()==ID_gcc_float128)
    gcc_float128_cnt++;
  else if(type.id()==ID_gcc_attribute_mode)
  {
    const exprt &size_expr=
      static_cast<const exprt &>(type.find(ID_size));
      
    if(size_expr.id()=="__QI__")
      gcc_mode_QI=true;
    else if(size_expr.id()=="__HI__")
      gcc_mode_HI=true;
    else if(size_expr.id()=="__SI__")
      gcc_mode_SI=true;
    else if(size_expr.id()=="__DI__")
      gcc_mode_DI=true;
    else
    {
      // we ignore without whining
    }
  }
  else if(type.id()==ID_bv)
  {
    bv_cnt++;
    const exprt &size_expr=
      static_cast<const exprt &>(type.find(ID_size));

    mp_integer size_int;
    if(to_integer(size_expr, size_int))
    {
      err_location(location);
      error("bit vector width has to be constant");
      throw 0;
    }
    
    if(size_int<1 || size_int>1024)
    {
      err_location(location);
      error("bit vector width invalid");
      throw 0;
    }
    
    bv_width=integer2long(size_int);
  }
  else if(type.id()==ID_short)
    short_cnt++;
  else if(type.id()==ID_long)
    long_cnt++;
  else if(type.id()==ID_double)
    double_cnt++;
  else if(type.id()==ID_float)
    float_cnt++;
  else if(type.id()==ID_bool)
    bool_cnt++;
  else if(type.id()==ID_complex)
    complex_cnt++;
  else if(type.id()==ID_static)
    c_storage_spec.is_static=true;
  else if(type.id()==ID_thread_local)
    c_storage_spec.is_thread_local=true;
  else if(type.id()==ID_inline)
    c_storage_spec.is_inline=true;
  else if(type.id()==ID_extern)
    c_storage_spec.is_extern=true;
  else if(type.id()==ID_typedef)
    c_storage_spec.is_typedef=true;
  else if(type.id()==ID_register)
    c_storage_spec.is_register=true;
  else if(type.id()==ID_auto)
  {
    // ignore
  }
  else if(type.id()==ID_packed)
    packed=true;
  else if(type.id()==ID_aligned)
  {
    aligned=true;

    // may come with size or not
    if(type.find(ID_size).is_nil())
      alignment=exprt(ID_default);
    else
      alignment=static_cast<const exprt &>(type.find(ID_size));
  }
  else if(type.id()==ID_transparent_union)
    transparent_union=true;
  else if(type.id()==ID_vector)
    vector_size=to_vector_type(type).size();
  else if(type.id()==ID_void)
  {
    // we store 'void' as 'empty'
    typet tmp=type;
    tmp.id(ID_empty);
    other.push_back(tmp);
  }
  else
    other.push_back(type);
}

/*******************************************************************\

Function: ansi_c_convert_typet::write

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_convert_typet::write(typet &type)
{
  type.clear();
  
  // first, do "other"

  if(!other.empty())
  {
    if(double_cnt || float_cnt || signed_cnt ||
       unsigned_cnt || int_cnt || bool_cnt ||
       short_cnt || char_cnt || complex_cnt || long_cnt ||
       int8_cnt || int16_cnt || int32_cnt || int64_cnt ||
       gcc_float128_cnt || bv_cnt)
    {
      err_location(location);
      error("illegal type modifier for defined type");
      throw 0;
    }

    if(other.size()!=1)
    {
      err_location(location);
      error("illegal combination of defined types");
      throw 0;
    }

    type.swap(other.front());
  }
  else if(gcc_float128_cnt)
  {
    if(signed_cnt || unsigned_cnt || int_cnt || bool_cnt ||
       int8_cnt || int16_cnt || int32_cnt || int64_cnt ||
       bv_cnt ||
       short_cnt || char_cnt)
    {
      err_location(location);
      error("cannot combine integer type with float");
      throw 0;
    }

    if(long_cnt || double_cnt || float_cnt)
    {
      err_location(location);
      error("conflicting type modifiers");
      throw 0;
    }
    
    type=long_double_type();
  }
  else if(double_cnt || float_cnt || complex_cnt)
  {
    if(signed_cnt || unsigned_cnt || int_cnt || bool_cnt ||
       int8_cnt || int16_cnt || int32_cnt || int64_cnt ||
       bv_cnt ||
       short_cnt || char_cnt)
    {
      err_location(location);
      error("cannot combine integer type with float or complex");
      throw 0;
    }

    if(double_cnt && float_cnt)
    {
      err_location(location);
      error("conflicting type modifiers");
      throw 0;
    }

    if(long_cnt==0)
    {
      if(double_cnt!=0)
        type=double_type();
      else
        type=float_type();
    }
    else if(long_cnt==1 || long_cnt==2)
    {
      if(double_cnt!=0)
        type=long_double_type();
      else
      {
        err_location(location);
        error("conflicting type modifiers");
        throw 0;
      }
    }
    else
    {
      err_location(location);
      error("illegal type modifier for float or complex");
      throw 0;
    }
  }
  else if(bool_cnt)
  {
    if(signed_cnt || unsigned_cnt || int_cnt || short_cnt ||
       int8_cnt || int16_cnt || int32_cnt || int64_cnt ||
       gcc_float128_cnt || bv_cnt ||
       char_cnt || long_cnt)
    {
      err_location(location);
      error("illegal type modifier for boolean type");
      throw 0;
    }

    type.id(ID_bool);
  }
  else
  {
    // it is integer -- signed or unsigned?

    if(signed_cnt && unsigned_cnt)
    {
      err_location(location);
      error("conflicting type modifiers");
      throw 0;
    }
    else if(unsigned_cnt)
      type.id(ID_unsignedbv);
    else if(signed_cnt)
      type.id(ID_signedbv);
    else
    {
      if(char_cnt)
        type.id(config.ansi_c.char_is_unsigned?ID_unsignedbv:ID_signedbv);
      else
        type.id(ID_signedbv);
    }

    // get width

    unsigned width;
    
    if(gcc_mode_QI || gcc_mode_HI || gcc_mode_SI || gcc_mode_DI)
    {
      if(gcc_mode_QI)
        width=1*8;
      else if(gcc_mode_HI)
        width=2*8;
      else if(gcc_mode_SI)
        width=4*8;
      else if(gcc_mode_DI)
        width=8*8;
      else
        assert(false);
    }
    else if(int8_cnt || int16_cnt || int32_cnt || int64_cnt || bv_cnt)
    {
      if(long_cnt || char_cnt || short_cnt)
      {
        err_location(location);
        error("conflicting type modifiers");
        throw 0;
      }
      
      if(int8_cnt)
        width=1*8;
      else if(int16_cnt)
        width=2*8;
      else if(int32_cnt)
        width=4*8;
      else if(int64_cnt)
        width=8*8;
      else if(bv_cnt)
        width=bv_width;
      else
        assert(false);
    }
    else if(short_cnt)
    {
      if(long_cnt || char_cnt)
      {
        err_location(location);
        error("conflicting type modifiers");
        throw 0;
      }

      width=config.ansi_c.short_int_width;
    }
    else if(char_cnt)
    {
      if(long_cnt)
      {
        err_location(location);
        error("illegal type modifier for char type");
        throw 0;
      }

      width=config.ansi_c.char_width;
    }
    else if(long_cnt==0)
    {
      width=config.ansi_c.int_width;
    }
    else if(long_cnt==1)
    {
      width=config.ansi_c.long_int_width;
    }
    else if(long_cnt==2)
    {
      width=config.ansi_c.long_long_int_width;
    }
    else
    {
      err_location(location);
      error("illegal type modifier for integer type");
      throw 0;
    }

    type.set(ID_width, width);
  }

  if(vector_size.is_not_nil())
  {
    vector_typet new_type;
    new_type.size()=vector_size;
    new_type.location()=vector_size.location();
    new_type.subtype().swap(type);
    type=new_type;
  }

  c_qualifiers.write(type);

  if(transparent_union)
    type.set(ID_transparent_union, true);

  if(packed)
    type.set(ID_C_packed, true);

  if(aligned)
    type.set(ID_C_alignment, alignment);
}
