/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "c_bit_field_replacement_type.h"

typet c_bit_field_replacement_type(
  const c_bit_field_typet &src,
  const namespacet &ns)
{
  const typet &subtype=src.subtype();

  if(subtype.id()==ID_unsignedbv ||
     subtype.id()==ID_signedbv ||
     subtype.id()==ID_c_bool)
  {
    bitvector_typet result=to_bitvector_type(subtype);
    result.set_width(src.get_width());
    return std::move(result);
  }
  else if(subtype.id()==ID_c_enum_tag)
  {
    const typet &sub_subtype=
      ns.follow_tag(to_c_enum_tag_type(subtype)).subtype();

    if(sub_subtype.id()==ID_signedbv ||
       sub_subtype.id()==ID_unsignedbv)
    {
      bitvector_typet result=to_bitvector_type(sub_subtype);
      result.set_width(src.get_width());
      return std::move(result);
    }
    else
      return nil_typet();
  }
  else
    return nil_typet();
}
