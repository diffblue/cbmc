/*******************************************************************\

Module: SpecC Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// SpecC Language Conversion

#include "ansi_c_convert_type.h"

#include <util/c_types.h>
#include <util/config.h>
#include <util/std_code.h>
#include <util/std_types.h>
#include <util/string_constant.h>

#include "gcc_types.h"

void ansi_c_convert_typet::read(const typet &type)
{
  clear();
  source_location=type.source_location();
  read_rec(type);
}

void ansi_c_convert_typet::read_rec(const typet &type)
{
  if(type.id()==ID_merged_type)
  {
    for(const typet &subtype : to_type_with_subtypes(type).subtypes())
      read_rec(subtype);
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
    // These can have up to 5 subtypes; we only use the first one.
    const auto &type_with_subtypes = to_type_with_subtypes(type);
    if(
      !type_with_subtypes.subtypes().empty() &&
      type_with_subtypes.subtypes()[0].id() == ID_string_constant)
      c_storage_spec.asm_label =
        to_string_constant(type_with_subtypes.subtypes()[0]).get_value();
  }
  else if(
    type.id() == ID_section && type.has_subtype() &&
    to_type_with_subtype(type).subtype().id() == ID_string_constant)
  {
    c_storage_spec.section =
      to_string_constant(to_type_with_subtype(type).subtype()).get_value();
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
    read_rec(to_type_with_subtype(type).subtype());
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
  else if(type.id()==ID_gcc_float16)
    gcc_float16_cnt++;
  else if(type.id()==ID_gcc_float32)
    gcc_float32_cnt++;
  else if(type.id()==ID_gcc_float32x)
    gcc_float32x_cnt++;
  else if(type.id()==ID_gcc_float64)
    gcc_float64_cnt++;
  else if(type.id()==ID_gcc_float64x)
    gcc_float64x_cnt++;
  else if(type.id()==ID_gcc_float128)
    gcc_float128_cnt++;
  else if(type.id()==ID_gcc_float128x)
    gcc_float128x_cnt++;
  else if(type.id()==ID_gcc_int128)
    gcc_int128_cnt++;
  else if(type.id()==ID_gcc_attribute_mode)
  {
    gcc_attribute_mode=type;
  }
  else if(type.id()==ID_msc_based)
  {
    const exprt &as_expr=
      static_cast<const exprt &>(static_cast<const irept &>(type));
    msc_based = to_unary_expr(as_expr).op();
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
  else if(type.id()==ID_weak)
    c_storage_spec.is_weak=true;
  else if(type.id() == ID_used)
    c_storage_spec.is_used = true;
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
  else if(type.id() == ID_frontend_vector)
  {
    // note that this is not yet a vector_typet -- this is a size only
    vector_size = static_cast<const constant_exprt &>(type.find(ID_size));
  }
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

      if(id==ID_thread)
        c_storage_spec.is_thread_local=true;
      else if(id=="align")
      {
        aligned=true;
        alignment = to_unary_expr(*it).op();
      }
    }
  }
  else if(type.id()==ID_noreturn)
    c_qualifiers.is_noreturn=true;
  else if(type.id()==ID_constructor)
    constructor=true;
  else if(type.id()==ID_destructor)
    destructor=true;
  else if(
    type.id() == ID_alias && type.has_subtype() &&
    to_type_with_subtype(type).subtype().id() == ID_string_constant)
  {
    c_storage_spec.alias =
      to_string_constant(to_type_with_subtype(type).subtype()).get_value();
  }
  else if(type.id()==ID_frontend_pointer)
  {
    // We turn ID_frontend_pointer to ID_pointer
    // Pointers have a width, much like integers,
    // which is added here.
    pointer_typet tmp(
      to_type_with_subtype(type).subtype(), config.ansi_c.pointer_width);
    tmp.add_source_location()=type.source_location();
    const irep_idt typedef_identifier=type.get(ID_C_typedef);
    if(!typedef_identifier.empty())
      tmp.set(ID_C_typedef, typedef_identifier);
    other.push_back(tmp);
  }
  else if(type.id()==ID_pointer)
  {
    UNREACHABLE;
  }
  else if(type.id() == ID_C_spec_requires)
  {
    const exprt &as_expr =
      static_cast<const exprt &>(static_cast<const irept &>(type));
    requires.push_back(to_unary_expr(as_expr).op());
  }
  else if(type.id() == ID_C_spec_assigns)
  {
    const exprt &as_expr =
      static_cast<const exprt &>(static_cast<const irept &>(type));

    for(const exprt &target : to_unary_expr(as_expr).op().operands())
      assigns.push_back(target);
  }
  else if(type.id() == ID_C_spec_ensures)
  {
    const exprt &as_expr =
      static_cast<const exprt &>(static_cast<const irept &>(type));
    ensures.push_back(to_unary_expr(as_expr).op());
  }
  else
    other.push_back(type);
}

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
       gcc_float16_cnt ||
       gcc_float32_cnt || gcc_float32x_cnt ||
       gcc_float64_cnt || gcc_float64x_cnt ||
       gcc_float128_cnt || gcc_float128x_cnt ||
       gcc_int128_cnt || bv_cnt)
    {
      error().source_location=source_location;
      error() << "illegal type modifier for defined type" << eom;
      throw 0;
    }

    // asm blocks (cf. regression/ansi-c/asm1) - ignore the asm
    if(other.size()==2)
    {
      if(other.front().id()==ID_asm && other.back().id()==ID_empty)
        other.pop_front();
      else if(other.front().id()==ID_empty && other.back().id()==ID_asm)
        other.pop_back();
    }

    if(other.size()!=1)
    {
      error().source_location=source_location;
      error() << "illegal combination of defined types" << eom;
      throw 0;
    }

    type.swap(other.front());

    // the contract expressions are meant for function types only
    if(!requires.empty())
      to_code_with_contract_type(type).requires() = std::move(requires);

    if(!assigns.empty())
      to_code_with_contract_type(type).assigns() = std::move(assigns);

    if(!ensures.empty())
      to_code_with_contract_type(type).ensures() = std::move(ensures);

    if(constructor || destructor)
    {
      if(constructor && destructor)
      {
        error().source_location=source_location;
        error() << "combining constructor and destructor not supported"
                << eom;
        throw 0;
      }

      typet *type_p=&type;
      if(type.id()==ID_code)
        type_p=&(to_code_type(type).return_type());

      else if(type_p->id()!=ID_empty)
      {
        error().source_location=source_location;
        error() << "constructor and destructor required to be type void, "
                << "found " << type_p->pretty() << eom;
        throw 0;
      }

      type_p->id(constructor ? ID_constructor : ID_destructor);
    }
  }
  else if(constructor || destructor)
  {
    error().source_location=source_location;
    error() << "constructor and destructor required to be type void, "
            << "found " << type.pretty() << eom;
    throw 0;
  }
  else if(gcc_float16_cnt ||
          gcc_float32_cnt || gcc_float32x_cnt ||
          gcc_float64_cnt || gcc_float64x_cnt ||
          gcc_float128_cnt || gcc_float128x_cnt)
  {
    if(signed_cnt || unsigned_cnt || int_cnt || c_bool_cnt || proper_bool_cnt ||
       int8_cnt || int16_cnt || int32_cnt || int64_cnt ||
       gcc_int128_cnt || bv_cnt ||
       short_cnt || char_cnt)
    {
      error().source_location=source_location;
      error() << "cannot combine integer type with floating-point type" << eom;
      throw 0;
    }

    if(long_cnt+double_cnt+
       float_cnt+gcc_float16_cnt+
       gcc_float32_cnt+gcc_float32x_cnt+
       gcc_float64_cnt+gcc_float64x_cnt+
       gcc_float128_cnt+gcc_float128x_cnt>=2)
    {
      error().source_location=source_location;
      error() << "conflicting type modifiers" << eom;
      throw 0;
    }

    // _not_ the same as float, double, long double
    if(gcc_float16_cnt)
      type=gcc_float16_type();
    else if(gcc_float32_cnt)
      type=gcc_float32_type();
    else if(gcc_float32x_cnt)
      type=gcc_float32x_type();
    else if(gcc_float64_cnt)
      type=gcc_float64_type();
    else if(gcc_float64x_cnt)
      type=gcc_float64x_type();
    else if(gcc_float128_cnt)
      type=gcc_float128_type();
    else if(gcc_float128x_cnt)
      type=gcc_float128x_type();
    else
      UNREACHABLE;
  }
  else if(double_cnt || float_cnt)
  {
    if(signed_cnt || unsigned_cnt || int_cnt || c_bool_cnt || proper_bool_cnt ||
       int8_cnt || int16_cnt || int32_cnt || int64_cnt ||
       gcc_int128_cnt|| bv_cnt ||
       short_cnt || char_cnt)
    {
      error().source_location=source_location;
      error() << "cannot combine integer type with floating-point type" << eom;
      throw 0;
    }

    if(double_cnt && float_cnt)
    {
      error().source_location=source_location;
      error() << "conflicting type modifiers" << eom;
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
        error().source_location=source_location;
        error() << "conflicting type modifiers" << eom;
        throw 0;
      }
    }
    else
    {
      error().source_location=source_location;
      error() << "illegal type modifier for float" << eom;
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
      error().source_location=source_location;
      error() << "illegal type modifier for C boolean type" << eom;
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
      error().source_location=source_location;
      error() << "illegal type modifier for proper boolean type" << eom;
      throw 0;
    }

    type.id(ID_bool);
  }
  else if(complex_cnt && !char_cnt && !signed_cnt && !unsigned_cnt &&
          !short_cnt && !gcc_int128_cnt)
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
      error().source_location=source_location;
      error() << "illegal type modifier for char type" << eom;
      throw 0;
    }

    if(signed_cnt && unsigned_cnt)
    {
      error().source_location=source_location;
      error() << "conflicting type modifiers" << eom;
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
      error().source_location=source_location;
      error() << "conflicting type modifiers" << eom;
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
        error().source_location=source_location;
        error() << "conflicting type modifiers" << eom;
        throw 0;
      }

      if(int8_cnt)
        if(is_signed)
          type=signed_char_type();
        else
          type=unsigned_char_type();
      else if(int16_cnt)
        if(is_signed)
          type=signed_short_int_type();
        else
          type=unsigned_short_int_type();
      else if(int32_cnt)
        if(is_signed)
          type=signed_int_type();
        else
          type=unsigned_int_type();
      else if(int64_cnt) // Visual Studio: equivalent to long long int
        if(is_signed)
          type=signed_long_long_int_type();
        else
          type=unsigned_long_long_int_type();
      else
        UNREACHABLE;
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
        error().source_location=source_location;
        error() << "conflicting type modifiers" << eom;
        throw 0;
      }

      if(is_signed)
        type=signed_short_int_type();
      else
        type=unsigned_short_int_type();
    }
    else if(long_cnt==0)
    {
      if(is_signed)
        type=signed_int_type();
      else
        type=unsigned_int_type();
    }
    else if(long_cnt==1)
    {
      if(is_signed)
        type=signed_long_int_type();
      else
        type=unsigned_long_int_type();
    }
    else if(long_cnt==2)
    {
      if(is_signed)
        type=signed_long_long_int_type();
      else
        type=unsigned_long_long_int_type();
    }
    else
    {
      error().source_location=source_location;
      error() << "illegal type modifier for integer type" << eom;
      throw 0;
    }
  }

  build_type_with_subtype(type);
  set_attributes(type);
}

/// Build a vector or complex type with \p type as subtype.
void ansi_c_convert_typet::build_type_with_subtype(typet &type) const
{
  if(vector_size.is_not_nil())
  {
    type_with_subtypet new_type(ID_frontend_vector, type);
    new_type.set(ID_size, vector_size);
    new_type.add_source_location()=vector_size.source_location();
    type=new_type;
  }

  if(complex_cnt)
  {
    // These take more or less arbitrary subtypes.
    complex_typet new_type(type);
    new_type.add_source_location()=source_location;
    type.swap(new_type);
  }
}

/// Add qualifiers and GCC attributes onto \p type.
void ansi_c_convert_typet::set_attributes(typet &type) const
{
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
