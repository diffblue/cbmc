/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "c_types.h"

#include "config.h"
#include "invariant.h"
#include "pointer_offset_size.h"
#include "std_types.h"

bitvector_typet c_index_type()
{
  // same as signed size type
  return signed_size_type();
}

bitvector_typet index_type()
{
  return c_index_type();
}

/// return type of enum constants
bitvector_typet c_enum_constant_type()
{
  // usually same as 'int',
  // but might be unsigned, or shorter than 'int'
  return signed_int_type();
}

bitvector_typet enum_constant_type()
{
  return c_enum_constant_type();
}

signedbv_typet signed_int_type()
{
  signedbv_typet result(config.ansi_c.int_width);
  result.set(ID_C_c_type, ID_signed_int);
  return result;
}

signedbv_typet signed_short_int_type()
{
  signedbv_typet result(config.ansi_c.short_int_width);
  result.set(ID_C_c_type, ID_signed_short_int);
  return result;
}

unsignedbv_typet unsigned_int_type()
{
  unsignedbv_typet result(config.ansi_c.int_width);
  result.set(ID_C_c_type, ID_unsigned_int);
  return result;
}

unsignedbv_typet unsigned_short_int_type()
{
  unsignedbv_typet result(config.ansi_c.short_int_width);
  result.set(ID_C_c_type, ID_unsigned_short_int);
  return result;
}

unsignedbv_typet size_type()
{
  // The size type varies. This is unsigned int on some systems,
  // and unsigned long int on others,
  // and unsigned long long on say Windows 64.

  if(config.ansi_c.pointer_width==config.ansi_c.int_width)
    return unsigned_int_type();
  else if(config.ansi_c.pointer_width==config.ansi_c.long_int_width)
    return unsigned_long_int_type();
  else if(config.ansi_c.pointer_width==config.ansi_c.long_long_int_width)
    return unsigned_long_long_int_type();
  else
    INVARIANT(false, "width of size type"); // aaah!
}

signedbv_typet signed_size_type()
{
  // we presume this is the same as pointer difference
  return pointer_diff_type();
}

signedbv_typet signed_long_int_type()
{
  signedbv_typet result(config.ansi_c.long_int_width);
  result.set(ID_C_c_type, ID_signed_long_int);
  return result;
}

signedbv_typet signed_long_long_int_type()
{
  signedbv_typet result(config.ansi_c.long_long_int_width);
  result.set(ID_C_c_type, ID_signed_long_long_int);
  return result;
}

unsignedbv_typet unsigned_long_int_type()
{
  unsignedbv_typet result(config.ansi_c.long_int_width);
  result.set(ID_C_c_type, ID_unsigned_long_int);
  return result;
}

unsignedbv_typet unsigned_long_long_int_type()
{
  unsignedbv_typet result(config.ansi_c.long_long_int_width);
  result.set(ID_C_c_type, ID_unsigned_long_long_int);
  return result;
}

typet c_bool_type()
{
  typet result=c_bool_typet(config.ansi_c.bool_width);
  return result;
}

bitvector_typet char_type()
{
  // this can be signed or unsigned, depending on the architecture

  // There are 3 char types, i.e., this one is
  // different from either signed char or unsigned char!

  if(config.ansi_c.char_is_unsigned)
  {
    unsignedbv_typet result(config.ansi_c.char_width);
    result.set(ID_C_c_type, ID_char);
    return std::move(result);
  }
  else
  {
    signedbv_typet result(config.ansi_c.char_width);
    result.set(ID_C_c_type, ID_char);
    return std::move(result);
  }
}

unsignedbv_typet unsigned_char_type()
{
  unsignedbv_typet result(config.ansi_c.char_width);
  result.set(ID_C_c_type, ID_unsigned_char);
  return result;
}

signedbv_typet signed_char_type()
{
  signedbv_typet result(config.ansi_c.char_width);
  result.set(ID_C_c_type, ID_signed_char);
  return result;
}

bitvector_typet wchar_t_type()
{
  if(config.ansi_c.wchar_t_is_unsigned)
  {
    unsignedbv_typet result(config.ansi_c.wchar_t_width);
    result.set(ID_C_c_type, ID_wchar_t);
    return std::move(result);
  }
  else
  {
    signedbv_typet result(config.ansi_c.wchar_t_width);
    result.set(ID_C_c_type, ID_wchar_t);
    return std::move(result);
  }
}

unsignedbv_typet char16_t_type()
{
  // Types char16_t and char32_t denote distinct types with the same size,
  // signedness, and alignment as uint_least16_t and uint_least32_t,
  // respectively, in <stdint.h>, called the underlying types.
  unsignedbv_typet result(16);
  result.set(ID_C_c_type, ID_char16_t);
  return result;
}

unsignedbv_typet char32_t_type()
{
  // Types char16_t and char32_t denote distinct types with the same size,
  // signedness, and alignment as uint_least16_t and uint_least32_t,
  // respectively, in <stdint.h>, called the underlying types.
  unsignedbv_typet result(32);
  result.set(ID_C_c_type, ID_char32_t);
  return result;
}

floatbv_typet float_type()
{
  floatbv_typet result=
    ieee_float_spect::single_precision().to_type();
  result.set(ID_C_c_type, ID_float);
  return result;
}

floatbv_typet double_type()
{
  floatbv_typet result=
    ieee_float_spect::double_precision().to_type();
  result.set(ID_C_c_type, ID_double);
  return result;
}

floatbv_typet long_double_type()
{
  floatbv_typet result;
  if(config.ansi_c.long_double_width==128)
    result=ieee_float_spect::quadruple_precision().to_type();
  else if(config.ansi_c.long_double_width==64)
    result=ieee_float_spect::double_precision().to_type();
  else if(config.ansi_c.long_double_width==80)
  {
    // x86 extended precision has 80 bits in total, and
    // deviating from IEEE, does not use a hidden bit.
    // We use the closest we have got, but the below isn't accurate.
    result=ieee_float_spect(63, 15).to_type();
  }
  else if(config.ansi_c.long_double_width==96)
  {
    result=ieee_float_spect(80, 15).to_type();
    // not quite right. The extra bits beyond 80 are usually padded.
  }
  else
    INVARIANT(false, "width of long double");

  result.set(ID_C_c_type, ID_long_double);

  return result;
}

signedbv_typet pointer_diff_type()
{
  // The pointer-diff type varies. This is signed int on some systems,
  // and signed long int on others, and signed long long on say Windows.

  if(config.ansi_c.pointer_width==config.ansi_c.int_width)
    return signed_int_type();
  else if(config.ansi_c.pointer_width==config.ansi_c.long_int_width)
    return signed_long_int_type();
  else if(config.ansi_c.pointer_width==config.ansi_c.long_long_int_width)
    return signed_long_long_int_type();
  else
    INVARIANT(false, "width of pointer difference");
}

pointer_typet pointer_type(const typet &subtype)
{
  return pointer_typet(subtype, config.ansi_c.pointer_width);
}

reference_typet reference_type(const typet &subtype)
{
  return reference_typet(subtype, config.ansi_c.pointer_width);
}

empty_typet void_type()
{
  static const auto result = empty_typet();
  return result;
}

std::string c_type_as_string(const irep_idt &c_type)
{
  if(c_type==ID_signed_int)
    return "signed int";
  else if(c_type==ID_signed_short_int)
    return "signed short int";
  else if(c_type==ID_unsigned_int)
    return "unsigned int";
  else if(c_type==ID_unsigned_short_int)
    return "unsigned short int";
  else if(c_type==ID_signed_long_int)
    return "signed long int";
  else if(c_type==ID_signed_long_long_int)
    return "signed long long int";
  else if(c_type==ID_unsigned_long_int)
    return "unsigned long int";
  else if(c_type==ID_unsigned_long_long_int)
    return "unsigned long long int";
  else if(c_type==ID_bool)
    return "_Bool";
  else if(c_type==ID_char)
    return "char";
  else if(c_type==ID_unsigned_char)
    return "unsigned char";
  else if(c_type==ID_signed_char)
    return "signed char";
  else if(c_type==ID_wchar_t)
    return "wchar_t";
  else if(c_type==ID_char16_t)
    return "char16_t";
  else if(c_type==ID_char32_t)
    return "char32_t";
  else if(c_type==ID_float)
    return "float";
  else if(c_type==ID_double)
    return "double";
  else if(c_type==ID_long_double)
    return "long double";
  else if(c_type==ID_gcc_float128)
    return "__float128";
  else if(c_type==ID_unsigned_int128)
    return "unsigned __int128";
  else if(c_type==ID_signed_int128)
    return "signed __int128";
  else
    return "";
}

optionalt<std::pair<struct_union_typet::componentt, mp_integer>>
union_typet::find_widest_union_component(const namespacet &ns) const
{
  const union_typet::componentst &comps = components();

  optionalt<mp_integer> max_width;
  typet max_comp_type;
  irep_idt max_comp_name;

  for(const auto &comp : comps)
  {
    auto element_width = pointer_offset_bits(comp.type(), ns);

    if(!element_width.has_value())
      return {};

    if(max_width.has_value() && *element_width <= *max_width)
      continue;

    max_width = *element_width;
    max_comp_type = comp.type();
    max_comp_name = comp.get_name();
  }

  if(!max_width.has_value())
    return {};
  else
    return std::make_pair(
      struct_union_typet::componentt{max_comp_name, max_comp_type}, *max_width);
}
