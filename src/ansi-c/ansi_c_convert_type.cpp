/*******************************************************************\

Module: SpecC Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/config.h>
#include <util/arith_tools.h>
#include <util/std_types.h>

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
  source_location=type.source_location();
  read_rec(type);

  if(!aligned &&
     type.find(ID_C_alignment).is_not_nil())
  {
    aligned=true;

    alignment=static_cast<const exprt &>(type.find(ID_C_alignment));
  }
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
    // These are called 'asm labels' by GCC.
    // ignore for now
  }
  else if(type.id()==ID_const)
    c_qualifiers.is_constant=true;
  else if(type.id()==ID_restrict)
    c_qualifiers.is_restricted=true;
  else if(type.id()==ID_atomic)
    c_qualifiers.is_atomic=true;
  else if(type.id()==ID_atomic_type_specifier)
  {
    // this gets turned into the qualifier, uh
    c_qualifiers.is_atomic=true;
    read_rec(type.subtype());
  }
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
  else if(type.id()==ID_gcc_int128)
    gcc_int128_cnt++;
  else if(type.id()==ID_gcc_attribute_mode)
  {
    gcc_attribute_mode=type;
  }
  else if(type.id()==ID_gcc_attribute)
  {
  }
  else if(type.id()==ID_msc_based)
  {
    const exprt &as_expr=static_cast<const exprt &>(static_cast<const irept &>(type));
    assert(as_expr.operands().size()==1);
    msc_based=as_expr.op0();
  }
  else if(type.id()==ID_custom_bv)
  {
    bv_cnt++;
    const exprt &size_expr=
      static_cast<const exprt &>(type.find(ID_size));
      
    bv_width=size_expr;
  }
  else if(type.id()==ID_custom_floatbv)
  {
    floatbv_cnt++;

    const exprt &size_expr=
      static_cast<const exprt &>(type.find(ID_size));
    const exprt &fsize_expr=
      static_cast<const exprt &>(type.find(ID_f));

    bv_width=size_expr;
    fraction_width=fsize_expr;
  }
  else if(type.id()==ID_custom_fixedbv)
  {
    fixedbv_cnt++;

    const exprt &size_expr=
      static_cast<const exprt &>(type.find(ID_size));
    const exprt &fsize_expr=
      static_cast<const exprt &>(type.find(ID_f));

    bv_width=size_expr;
    fraction_width=fsize_expr;
  }
  else if(type.id()==ID_short)
    short_cnt++;
  else if(type.id()==ID_long)
    long_cnt++;
  else if(type.id()==ID_double)
    double_cnt++;
  else if(type.id()==ID_float)
    float_cnt++;
  else if(type.id()==ID_c_bool)
    c_bool_cnt++;
  else if(type.id()==ID_proper_bool)
    proper_bool_cnt++;
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
  {
    c_qualifiers.is_transparent_union=true;
  }
  else if(type.id()==ID_vector)
    vector_size=to_vector_type(type).size();
  else if(type.id()==ID_void)
  {
    // we store 'void' as 'empty'
    typet tmp=type;
    tmp.id(ID_empty);
    other.push_back(tmp);
  }
  else if(type.id()==ID_msc_declspec)
  {
    const exprt &as_expr=
      static_cast<const exprt &>(static_cast<const irept &>(type));
      
    forall_operands(it, as_expr)
    {
      // these are symbols
      const irep_idt &id=it->get(ID_identifier);

      if(id=="thread")
        c_storage_spec.is_thread_local=true;
      else if(id=="align")
      {
        assert(it->operands().size()==1);
        aligned=true;
        alignment=it->op0();
      }
    }
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
       unsigned_cnt || int_cnt || c_bool_cnt || proper_bool_cnt ||
       short_cnt || char_cnt || complex_cnt || long_cnt ||
       int8_cnt || int16_cnt || int32_cnt || int64_cnt ||
       gcc_float128_cnt || gcc_int128_cnt || bv_cnt)
    {
      err_location(source_location);
      error("illegal type modifier for defined type");
      throw 0;
    }

    if(other.size()!=1)
    {
      err_location(source_location);
      error("illegal combination of defined types");
      throw 0;
    }

    type.swap(other.front());
  }
  else if(gcc_float128_cnt)
  {
    if(signed_cnt || unsigned_cnt || int_cnt || c_bool_cnt || proper_bool_cnt ||
       int8_cnt || int16_cnt || int32_cnt || int64_cnt ||
       gcc_int128_cnt || bv_cnt ||
       short_cnt || char_cnt)
    {
      err_location(source_location);
      error("cannot combine integer type with float");
      throw 0;
    }

    if(long_cnt || double_cnt || float_cnt)
    {
      err_location(source_location);
      error("conflicting type modifiers");
      throw 0;
    }

    // _not_ the same as long double
    type=gcc_float128_type();
  }
  else if(double_cnt || float_cnt)
  {
    if(signed_cnt || unsigned_cnt || int_cnt || c_bool_cnt || proper_bool_cnt ||
       int8_cnt || int16_cnt || int32_cnt || int64_cnt ||
       gcc_int128_cnt|| bv_cnt ||
       short_cnt || char_cnt)
    {
      err_location(source_location);
      error("cannot combine integer type with float");
      throw 0;
    }

    if(double_cnt && float_cnt)
    {
      err_location(source_location);
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
        err_location(source_location);
        error("conflicting type modifiers");
        throw 0;
      }
    }
    else
    {
      err_location(source_location);
      error("illegal type modifier for float");
      throw 0;
    }
  }
  else if(c_bool_cnt)
  {
    if(signed_cnt || unsigned_cnt || int_cnt || short_cnt ||
       int8_cnt || int16_cnt || int32_cnt || int64_cnt ||
       gcc_float128_cnt || bv_cnt || proper_bool_cnt ||
       char_cnt || long_cnt)
    {
      err_location(source_location);
      error("illegal type modifier for C boolean type");
      throw 0;
    }

    type=c_bool_type();
  }
  else if(proper_bool_cnt)
  {
    if(signed_cnt || unsigned_cnt || int_cnt || short_cnt ||
       int8_cnt || int16_cnt || int32_cnt || int64_cnt ||
       gcc_float128_cnt || bv_cnt ||
       char_cnt || long_cnt)
    {
      err_location(source_location);
      error("illegal type modifier for proper boolean type");
      throw 0;
    }

    type.id(ID_bool);
  }
  else if(complex_cnt && !char_cnt && !signed_cnt && !unsigned_cnt && !short_cnt && !gcc_int128_cnt)
  {
    // the "default" for complex is double
    type=double_type();
  }
  else if(char_cnt)
  {
    if(int_cnt || short_cnt || long_cnt ||
       int8_cnt || int16_cnt || int32_cnt || int64_cnt ||
       gcc_float128_cnt || bv_cnt || proper_bool_cnt)
    {
      err_location(source_location);
      error("illegal type modifier for char type");
      throw 0;
    }

    if(signed_cnt && unsigned_cnt)
    {
      err_location(source_location);
      error("conflicting type modifiers");
      throw 0;
    }
    else if(unsigned_cnt)
      type=unsigned_char_type();
    else if(signed_cnt)
      type=signed_char_type();
    else
      type=char_type();
  }
  else
  {
    // it is integer -- signed or unsigned?
    
    bool is_signed=true; // default

    if(signed_cnt && unsigned_cnt)
    {
      err_location(source_location);
      error("conflicting type modifiers");
      throw 0;
    }
    else if(unsigned_cnt)
      is_signed=false;
    else if(signed_cnt)
      is_signed=true;

    if(int8_cnt || int16_cnt || int32_cnt || int64_cnt)
    {
      if(long_cnt || char_cnt || short_cnt || gcc_int128_cnt || bv_cnt)
      {
        err_location(source_location);
        error("conflicting type modifiers");
        throw 0;
      }
      
      if(int8_cnt)
        type=is_signed?signed_char_type():unsigned_char_type();
      else if(int16_cnt)
        type=is_signed?signed_short_int_type():unsigned_short_int_type();
      else if(int32_cnt)
        type=is_signed?signed_int_type():unsigned_int_type();
      else if(int64_cnt) // Visual Studio: equivalent to long long int
        type=is_signed?signed_long_long_int_type():unsigned_long_long_int_type();
      else
        assert(false);
    }
    else if(gcc_int128_cnt)
    {
      if(is_signed)
        type=gcc_signed_int128_type();
      else
        type=gcc_unsigned_int128_type();
    }
    else if(bv_cnt)
    {
      // explicitly-given expression for width
      type.id(is_signed?ID_custom_signedbv:ID_custom_unsignedbv);
      type.set(ID_size, bv_width);
    }
    else if(floatbv_cnt)
    {
      type.id(ID_custom_floatbv);
      type.set(ID_size, bv_width);
      type.set(ID_f, fraction_width);
    }
    else if(fixedbv_cnt)
    {
      type.id(ID_custom_fixedbv);
      type.set(ID_size, bv_width);
      type.set(ID_f, fraction_width);
    }
    else if(short_cnt)
    {
      if(long_cnt || char_cnt)
      {
        err_location(source_location);
        error("conflicting type modifiers");
        throw 0;
      }

      type=is_signed?signed_short_int_type():unsigned_short_int_type();
    }
    else if(long_cnt==0)
    {
      type=is_signed?signed_int_type():unsigned_int_type();
    }
    else if(long_cnt==1)
    {
      type=is_signed?signed_long_int_type():unsigned_long_int_type();
    }
    else if(long_cnt==2)
    {
      type=is_signed?signed_long_long_int_type():unsigned_long_long_int_type();
    }
    else
    {
      err_location(source_location);
      error("illegal type modifier for integer type");
      throw 0;
    }
  }

  if(vector_size.is_not_nil())
  {
    vector_typet new_type;
    new_type.size()=vector_size;
    new_type.add_source_location()=vector_size.source_location();
    new_type.subtype().swap(type);
    type=new_type;
  }
  
  if(complex_cnt)
  {
    // These take more or less arbitrary subtypes.
    complex_typet new_type;
    new_type.add_source_location()=source_location;
    new_type.subtype()=type;
    type.swap(new_type);
  }

  if(gcc_attribute_mode.is_not_nil())
  {
    typet new_type=gcc_attribute_mode;
    new_type.subtype()=type;
    type.swap(new_type);
  }
  
  c_qualifiers.write(type);

  if(packed)
    type.set(ID_C_packed, true);

  if(aligned)
    type.set(ID_C_alignment, alignment);
}
