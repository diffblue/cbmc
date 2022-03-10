/*******************************************************************\

Module: API to expression classes for Pointers

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "pointer_expr.h"

#include "arith_tools.h"
#include "byte_operators.h"
#include "c_types.h"
#include "expr_util.h"
#include "pointer_offset_size.h"
#include "simplify_expr.h"

void dynamic_object_exprt::set_instance(unsigned int instance)
{
  op0() = from_integer(instance, typet(ID_natural));
}

unsigned int dynamic_object_exprt::get_instance() const
{
  return std::stoul(id2string(to_constant_expr(op0()).get_value()));
}

/// Build an object_descriptor_exprt from a given expr
static void build_object_descriptor_rec(
  const namespacet &ns,
  const exprt &expr,
  object_descriptor_exprt &dest)
{
  if(expr.id() == ID_index)
  {
    const index_exprt &index = to_index_expr(expr);

    build_object_descriptor_rec(ns, index.array(), dest);

    auto sub_size = size_of_expr(expr.type(), ns);
    CHECK_RETURN(sub_size.has_value());

    dest.offset() = plus_exprt(
      dest.offset(),
      mult_exprt(
        typecast_exprt::conditional_cast(index.index(), c_index_type()),
        typecast_exprt::conditional_cast(sub_size.value(), c_index_type())));
  }
  else if(expr.id() == ID_member)
  {
    const member_exprt &member = to_member_expr(expr);
    const exprt &struct_op = member.struct_op();

    build_object_descriptor_rec(ns, struct_op, dest);

    auto offset = member_offset_expr(member, ns);
    CHECK_RETURN(offset.has_value());

    dest.offset() = plus_exprt(
      dest.offset(),
      typecast_exprt::conditional_cast(offset.value(), c_index_type()));
  }
  else if(
    expr.id() == ID_byte_extract_little_endian ||
    expr.id() == ID_byte_extract_big_endian)
  {
    const byte_extract_exprt &be = to_byte_extract_expr(expr);

    dest.object() = be.op();

    build_object_descriptor_rec(ns, be.op(), dest);

    dest.offset() = plus_exprt(
      dest.offset(),
      typecast_exprt::conditional_cast(
        to_byte_extract_expr(expr).offset(), c_index_type()));
  }
  else if(expr.id() == ID_typecast)
  {
    const typecast_exprt &tc = to_typecast_expr(expr);

    dest.object() = tc.op();

    build_object_descriptor_rec(ns, tc.op(), dest);
  }
  else if(const auto deref = expr_try_dynamic_cast<dereference_exprt>(expr))
  {
    const exprt &pointer = skip_typecast(deref->pointer());
    if(const auto address_of = expr_try_dynamic_cast<address_of_exprt>(pointer))
    {
      dest.object() = address_of->object();
      build_object_descriptor_rec(ns, address_of->object(), dest);
    }
  }
  else if(const auto address_of = expr_try_dynamic_cast<address_of_exprt>(expr))
  {
    const exprt &object = skip_typecast(address_of->object());
    if(const auto deref = expr_try_dynamic_cast<dereference_exprt>(object))
    {
      dest.object() = deref->pointer();
      build_object_descriptor_rec(ns, deref->pointer(), dest);
    }
  }
}

/// Build an object_descriptor_exprt from a given expr
void object_descriptor_exprt::build(const exprt &expr, const namespacet &ns)
{
  PRECONDITION(object().id() == ID_unknown);
  object() = expr;

  if(offset().id() == ID_unknown)
    offset() = from_integer(0, c_index_type());

  build_object_descriptor_rec(ns, expr, *this);
  simplify(offset(), ns);
}

address_of_exprt::address_of_exprt(const exprt &_op)
  : unary_exprt(ID_address_of, _op, pointer_type(_op.type()))
{
}

object_address_exprt::object_address_exprt(const symbol_exprt &object)
  : nullary_exprt(ID_object_address, pointer_type(object.type()))
{
  set(ID_identifier, object.get_identifier());
}

symbol_exprt object_address_exprt::object_expr() const
{
  return symbol_exprt(object_identifier(), to_pointer_type(type()).base_type());
}

field_address_exprt::field_address_exprt(
  exprt compound_ptr,
  const irep_idt &component_name,
  pointer_typet _type)
  : unary_exprt(ID_field_address, std::move(compound_ptr), std::move(_type))
{
  const auto &base_type = field_address_exprt::base().type();
  PRECONDITION(base_type.id() == ID_pointer);
  const auto &compound_type = to_pointer_type(base_type).base_type();
  PRECONDITION(
    compound_type.id() == ID_struct || compound_type.id() == ID_struct_tag ||
    compound_type.id() == ID_union || compound_type.id() == ID_union_tag);
  set(ID_component_name, component_name);
}

element_address_exprt::element_address_exprt(const exprt &base, exprt index)
  : binary_exprt(
      base,
      ID_element_address,
      std::move(index),
      pointer_typet(
        to_pointer_type(base.type()).base_type(),
        to_pointer_type(base.type()).get_width()))
{
}

const exprt &object_descriptor_exprt::root_object(const exprt &expr)
{
  const exprt *p = &expr;

  while(true)
  {
    if(p->id() == ID_member)
      p = &to_member_expr(*p).compound();
    else if(p->id() == ID_index)
      p = &to_index_expr(*p).array();
    else
      break;
  }

  return *p;
}

/// Check that the dereference expression has the right number of operands,
/// refers to something with a pointer type, and that its type is the base type
/// of that pointer type. Throws or raises an invariant if not, according to
/// validation mode.
/// \param expr: expression to validate
/// \param ns: global namespace
/// \param vm: validation mode (see \ref exprt::validate)
void dereference_exprt::validate(
  const exprt &expr,
  const namespacet &ns,
  const validation_modet vm)
{
  check(expr, vm);

  const auto &dereference_expr = to_dereference_expr(expr);

  const typet &type_of_operand = dereference_expr.pointer().type();

  const pointer_typet *pointer_type =
    type_try_dynamic_cast<pointer_typet>(type_of_operand);

  DATA_CHECK(
    vm,
    pointer_type,
    "dereference expression's operand must have a pointer type");

  DATA_CHECK(
    vm,
    dereference_expr.type() == pointer_type->base_type(),
    "dereference expression's type must match the base type of the type of its "
    "operand");
}
