/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "c_bit_field_replacement_type.h"

#include <util/c_types.h>
#include <util/invariant.h>
#include <util/namespace.h>

typet c_bit_field_replacement_type(
  const c_bit_field_typet &src,
  const namespacet &ns)
{
  const typet &underlying_type = src.underlying_type();

  if(
    underlying_type.id() == ID_unsignedbv ||
    underlying_type.id() == ID_signedbv || underlying_type.id() == ID_c_bool)
  {
    bitvector_typet result = to_bitvector_type(underlying_type);
    result.set_width(src.get_width());
    return std::move(result);
  }
  else
  {
    PRECONDITION(underlying_type.id() == ID_c_enum_tag);

    const typet &sub_subtype =
      ns.follow_tag(to_c_enum_tag_type(underlying_type)).underlying_type();

    PRECONDITION(
      sub_subtype.id() == ID_signedbv || sub_subtype.id() == ID_unsignedbv);

    bitvector_typet result = to_bitvector_type(sub_subtype);
    result.set_width(src.get_width());
    return std::move(result);
  }
}
