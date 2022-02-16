/*******************************************************************\

Module: Pointer Logic

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Logic

#include "pointer_logic.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/invariant.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

bool pointer_logict::is_dynamic_object(const exprt &expr) const
{
  return expr.type().get_bool(ID_C_dynamic) ||
         (expr.id() == ID_symbol &&
          has_prefix(
            id2string(to_symbol_expr(expr).get_identifier()),
            SYMEX_DYNAMIC_PREFIX));
}

void pointer_logict::get_dynamic_objects(std::vector<std::size_t> &o) const
{
  o.clear();
  std::size_t nr=0;

  for(auto it = objects.cbegin(); it != objects.cend(); ++it, ++nr)
    if(is_dynamic_object(*it))
      o.push_back(nr);
}

std::size_t pointer_logict::add_object(const exprt &expr)
{
  // remove any index/member

  if(expr.id()==ID_index)
  {
    return add_object(to_index_expr(expr).array());
  }
  else if(expr.id()==ID_member)
  {
    return add_object(to_member_expr(expr).compound());
  }

  return objects.number(expr);
}

exprt pointer_logict::pointer_expr(
  std::size_t object,
  const pointer_typet &type) const
{
  pointert pointer(object, 0);
  return pointer_expr(pointer, type);
}

exprt pointer_logict::pointer_expr(
  const pointert &pointer,
  const pointer_typet &type) const
{
  if(pointer.object==null_object) // NULL?
  {
    if(pointer.offset==0)
    {
      return null_pointer_exprt(type);
    }
    else
    {
      null_pointer_exprt null(type);
      return plus_exprt(null,
        from_integer(pointer.offset, pointer_diff_type()));
    }
  }
  else if(pointer.object==invalid_object) // INVALID?
  {
    return constant_exprt("INVALID", type);
  }

  if(pointer.object>=objects.size())
  {
    return constant_exprt("INVALID-" + std::to_string(pointer.object), type);
  }

  const exprt &object_expr=objects[pointer.object];

  typet subtype = type.base_type();
  // This is a gcc extension.
  // https://gcc.gnu.org/onlinedocs/gcc-4.8.0/gcc/Pointer-Arith.html
  if(subtype.id() == ID_empty)
    subtype = char_type();
  if(object_expr.id() == ID_string_constant)
  {
    subtype = object_expr.type();

    // a string constant must be array-typed with fixed size
    const array_typet &array_type = to_array_type(object_expr.type());
    mp_integer array_size =
      numeric_cast_v<mp_integer>(to_constant_expr(array_type.size()));
    if(array_size > pointer.offset)
    {
      to_array_type(subtype).size() =
        from_integer(array_size - pointer.offset, array_type.size().type());
    }
  }
  auto deep_object_opt =
    get_subexpression_at_offset(object_expr, pointer.offset, subtype, ns);
  CHECK_RETURN(deep_object_opt.has_value());
  exprt deep_object = deep_object_opt.value();
  simplify(deep_object, ns);
  if(
    deep_object.id() != ID_byte_extract_little_endian &&
    deep_object.id() != ID_byte_extract_big_endian)
  {
    return typecast_exprt::conditional_cast(
      address_of_exprt(deep_object), type);
  }

  const byte_extract_exprt &be = to_byte_extract_expr(deep_object);
  const address_of_exprt base(be.op());
  if(be.offset().is_zero())
    return typecast_exprt::conditional_cast(base, type);

  const auto object_size = pointer_offset_size(be.op().type(), ns);
  if(object_size.has_value() && *object_size <= 1)
  {
    return typecast_exprt::conditional_cast(
      plus_exprt(base, from_integer(pointer.offset, pointer_diff_type())),
      type);
  }
  else if(object_size.has_value() && pointer.offset % *object_size == 0)
  {
    return typecast_exprt::conditional_cast(
      plus_exprt(
        base, from_integer(pointer.offset / *object_size, pointer_diff_type())),
      type);
  }
  else
  {
    return typecast_exprt::conditional_cast(
      plus_exprt(
        typecast_exprt(base, pointer_type(char_type())),
        from_integer(pointer.offset, pointer_diff_type())),
      type);
  }
}

pointer_logict::pointer_logict(const namespacet &_ns):ns(_ns)
{
  // add NULL
  null_object=objects.number(exprt(ID_NULL));
  CHECK_RETURN(null_object == 0);

  // add INVALID
  invalid_object=objects.number(exprt("INVALID"));
}

pointer_logict::~pointer_logict()
{
}
