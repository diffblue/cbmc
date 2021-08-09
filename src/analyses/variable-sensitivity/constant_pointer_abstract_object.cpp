/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include "constant_pointer_abstract_object.h"

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>

#include <ostream>

#include "abstract_object_statistics.h"

constant_pointer_abstract_objectt::constant_pointer_abstract_objectt(
  const typet &type)
  : abstract_pointer_objectt(type)
{
  PRECONDITION(type.id() == ID_pointer);
}

constant_pointer_abstract_objectt::constant_pointer_abstract_objectt(
  const typet &type,
  bool top,
  bool bottom)
  : abstract_pointer_objectt(type, top, bottom)
{
  PRECONDITION(type.id() == ID_pointer);
}

constant_pointer_abstract_objectt::constant_pointer_abstract_objectt(
  const typet &new_type,
  const constant_pointer_abstract_objectt &old)
  : abstract_pointer_objectt(new_type, old.is_top(), old.is_bottom()),
    value_stack(old.value_stack)
{
}

constant_pointer_abstract_objectt::constant_pointer_abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_pointer_objectt(expr, environment, ns),
    value_stack(expr, environment, ns)
{
  PRECONDITION(expr.type().id() == ID_pointer);
  if(value_stack.is_top_value())
  {
    set_top();
  }
  else
  {
    set_not_top();
  }
}

abstract_object_pointert constant_pointer_abstract_objectt::merge(
  const abstract_object_pointert &other,
  const widen_modet &widen_mode) const
{
  auto cast_other =
    std::dynamic_pointer_cast<const constant_pointer_abstract_objectt>(other);
  if(cast_other)
    return merge_constant_pointers(cast_other, widen_mode);

  return abstract_pointer_objectt::merge(other, widen_mode);
}

bool constant_pointer_abstract_objectt::same_target(
  abstract_object_pointert other) const
{
  auto cast_other =
    std::dynamic_pointer_cast<const constant_pointer_abstract_objectt>(other);

  if(value_stack.is_top_value() || cast_other->value_stack.is_top_value())
    return false;

  if(value_stack.depth() != cast_other->value_stack.depth())
    return false;

  for(size_t d = 0; d != value_stack.depth() - 1; ++d)
    if(
      value_stack.target_expression(d) !=
      cast_other->value_stack.target_expression(d))
      return false;

  return true;
}

exprt constant_pointer_abstract_objectt::offset() const
{
  if(value_stack.is_top_value())
    return nil_exprt();
  return value_stack.offset_expression();
}

exprt constant_pointer_abstract_objectt::offset_from(
  abstract_object_pointert other) const
{
  auto cast_other =
    std::dynamic_pointer_cast<const constant_pointer_abstract_objectt>(other);

  if(value_stack.is_top_value() || cast_other->value_stack.is_top_value())
    return nil_exprt();

  return minus_exprt(
    value_stack.offset_expression(),
    cast_other->value_stack.offset_expression());
}

abstract_object_pointert
constant_pointer_abstract_objectt::merge_constant_pointers(
  const constant_pointer_abstract_pointert &other,
  const widen_modet &widen_mode) const
{
  if(is_bottom())
    return std::make_shared<constant_pointer_abstract_objectt>(*other);

  bool matching_pointers =
    value_stack.to_expression() == other->value_stack.to_expression();

  if(matching_pointers)
    return shared_from_this();

  return abstract_pointer_objectt::merge(other, widen_mode);
}

exprt constant_pointer_abstract_objectt::to_constant() const
{
  if(is_top() || is_bottom())
  {
    return abstract_pointer_objectt::to_constant();
  }
  else
  {
    // TODO(tkiley): I think we would like to eval this before using it
    // in the to_constant.
    return value_stack.to_expression();
  }
}

void constant_pointer_abstract_objectt::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  if(is_top() || is_bottom() || value_stack.is_top_value())
  {
    abstract_pointer_objectt::output(out, ai, ns);
  }
  else
  {
    out << "ptr ->(";
    const exprt &value = value_stack.to_expression();
    if(value.id() == ID_address_of)
    {
      const auto &addressee = to_address_of_expr(value).object();
      if(addressee.id() == ID_symbol)
      {
        const symbol_exprt &symbol_pointed_to(to_symbol_expr(addressee));

        out << symbol_pointed_to.get_identifier();
      }
      else if(addressee.id() == ID_dynamic_object)
      {
        out << addressee.get(ID_identifier);
      }
      else if(addressee.id() == ID_index)
      {
        auto const &array_index = to_index_expr(addressee);
        auto const &array = array_index.array();
        if(array.id() == ID_symbol)
        {
          auto const &array_symbol = to_symbol_expr(array);
          out << array_symbol.get_identifier() << "[";
          if(array_index.index().id() == ID_constant)
            out << to_constant_expr(array_index.index()).get_value();
          else
            out << "?";
          out << "]";
        }
      }
    }

    out << ")";
  }
}

abstract_object_pointert constant_pointer_abstract_objectt::read_dereference(
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  if(is_top() || is_bottom() || value_stack.is_top_value())
  {
    // Return top if dereferencing a null pointer or we are top
    bool is_value_top = is_top() || value_stack.is_top_value();
    return env.abstract_object_factory(
      type().subtype(), ns, is_value_top, !is_value_top);
  }
  else
  {
    return env.eval(
      to_address_of_expr(value_stack.to_expression()).object(), ns);
  }
}

abstract_object_pointert constant_pointer_abstract_objectt::write_dereference(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const abstract_object_pointert &new_value,
  bool merging_write) const
{
  if(is_top() || is_bottom())
  {
    environment.havoc("Writing to a 2value pointer");
    return shared_from_this();
  }

  if(value_stack.is_top_value())
    return std::make_shared<constant_pointer_abstract_objectt>(
      type(), true, false);

  if(stack.empty())
  {
    // We should not be changing the type of an abstract object
    PRECONDITION(new_value->type() == ns.follow(type().subtype()));

    // Get an expression that we can assign to
    exprt value = to_address_of_expr(value_stack.to_expression()).object();
    if(merging_write)
    {
      abstract_object_pointert pointed_value = environment.eval(value, ns);
      abstract_object_pointert merged_value =
        abstract_objectt::merge(pointed_value, new_value, widen_modet::no)
          .object;
      environment.assign(value, merged_value, ns);
    }
    else
    {
      environment.assign(value, new_value, ns);
    }
  }
  else
  {
    exprt value = to_address_of_expr(value_stack.to_expression()).object();
    abstract_object_pointert pointed_value = environment.eval(value, ns);
    abstract_object_pointert modified_value =
      environment.write(pointed_value, new_value, stack, ns, merging_write);
    environment.assign(value, modified_value, ns);
    // but the pointer itself does not change!
  }

  return shared_from_this();
}

abstract_object_pointert constant_pointer_abstract_objectt::typecast(
  const typet &new_type,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  INVARIANT(is_void_pointer(type()), "Only allow pointer casting from void*");

  // Get an expression that we can assign to
  exprt value = to_address_of_expr(value_stack.to_expression()).object();
  if(value.id() == ID_dynamic_object)
  {
    auto &env = const_cast<abstract_environmentt &>(environment);

    auto heap_array_type = array_typet(new_type.subtype(), nil_exprt());
    auto array_object =
      environment.abstract_object_factory(heap_array_type, ns, true, false);
    auto heap_symbol = symbol_exprt(value.get(ID_identifier), heap_array_type);
    env.assign(heap_symbol, array_object, ns);
    auto heap_address = address_of_exprt(
      index_exprt(heap_symbol, from_integer(0, signed_size_type())));
    auto new_pointer = std::make_shared<constant_pointer_abstract_objectt>(
      heap_address, env, ns);
    return new_pointer;
  }

  return std::make_shared<constant_pointer_abstract_objectt>(new_type, *this);
}

void constant_pointer_abstract_objectt::get_statistics(
  abstract_object_statisticst &statistics,
  abstract_object_visitedt &visited,
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  abstract_pointer_objectt::get_statistics(statistics, visited, env, ns);
  // don't bother following nullptr
  if(!is_top() && !is_bottom() && !value_stack.is_top_value())
  {
    read_dereference(env, ns)->get_statistics(statistics, visited, env, ns);
  }
  statistics.objects_memory_usage += memory_sizet::from_bytes(sizeof(*this));
}

abstract_object_pointert constant_pointer_abstract_objectt::ptr_diff(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  auto &rhs = operands.back();

  if(same_target(rhs))
    return environment.eval(offset_from(rhs), ns);

  return abstract_objectt::expression_transform(
    expr, operands, environment, ns);
}

static exprt to_bool_expr(bool v)
{
  if(v)
    return true_exprt();
  return false_exprt();
}

exprt struct_member_ptr_comparison_expr(
  irep_idt const &id,
  exprt const &lhs,
  exprt const &rhs)
{
  auto const &lhs_member = to_member_expr(lhs).get_component_name();
  auto const &rhs_member = to_member_expr(rhs).get_component_name();

  if(id == ID_equal)
    return to_bool_expr(lhs_member == rhs_member);
  if(id == ID_notequal)
    return to_bool_expr(lhs_member != rhs_member);
  return nil_exprt();
}

exprt symbol_ptr_comparison_expr(
  irep_idt const &id,
  exprt const &lhs,
  exprt const &rhs)
{
  auto const &lhs_identifier = to_symbol_expr(lhs).get_identifier();
  auto const &rhs_identifier = to_symbol_expr(rhs).get_identifier();

  if(id == ID_equal)
    return to_bool_expr(lhs_identifier == rhs_identifier);
  if(id == ID_notequal)
    return to_bool_expr(lhs_identifier != rhs_identifier);
  return nil_exprt();
}

exprt constant_pointer_abstract_objectt::ptr_comparison_expr(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  auto rhs = std::dynamic_pointer_cast<const constant_pointer_abstract_objectt>(
    operands.back());

  if(is_top() || rhs->is_top())
    return nil_exprt();

  if(same_target(rhs)) // rewrite in terms of pointer offset
  {
    auto lhs_offset = offset();
    auto rhs_offset = rhs->offset();

    if(lhs_offset.id() == ID_member)
      return struct_member_ptr_comparison_expr(
        expr.id(), lhs_offset, rhs_offset);
    if(lhs_offset.id() == ID_symbol)
      return symbol_ptr_comparison_expr(expr.id(), lhs_offset, rhs_offset);

    return binary_relation_exprt(lhs_offset, expr.id(), rhs_offset);
  }

  // not same target, can only eval == and !=
  if(expr.id() == ID_equal)
    return false_exprt();
  if(expr.id() == ID_notequal)
    return true_exprt();
  return nil_exprt();
}

exprt constant_pointer_abstract_objectt::to_predicate_internal(
  const exprt &name) const
{
  return equal_exprt(name, value_stack.to_expression());
}
