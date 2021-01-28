/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include "constant_pointer_abstract_object.h"

#include <analyses/ai.h>
#include <analyses/variable-sensitivity/abstract_environment.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <ostream>

constant_pointer_abstract_objectt::constant_pointer_abstract_objectt(
  const typet &type)
  : pointer_abstract_objectt(type)
{
  PRECONDITION(type.id() == ID_pointer);
}

constant_pointer_abstract_objectt::constant_pointer_abstract_objectt(
  const typet &type,
  bool top,
  bool bottom)
  : pointer_abstract_objectt(type, top, bottom)
{
  PRECONDITION(type.id() == ID_pointer);
}

constant_pointer_abstract_objectt::constant_pointer_abstract_objectt(
  const constant_pointer_abstract_objectt &old)
  : pointer_abstract_objectt(old), value_stack(old.value_stack)
{
}

constant_pointer_abstract_objectt::constant_pointer_abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : pointer_abstract_objectt(expr, environment, ns),
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

abstract_object_pointert
constant_pointer_abstract_objectt::merge(abstract_object_pointert other) const
{
  auto cast_other =
    std::dynamic_pointer_cast<const constant_pointer_abstract_objectt>(other);
  if(cast_other)
  {
    return merge_constant_pointers(cast_other);
  }
  else
  {
    // TODO(tkiley): How do we set the result to be toppish?
    return pointer_abstract_objectt::merge(other);
  }
}

abstract_object_pointert
constant_pointer_abstract_objectt::merge_constant_pointers(
  const constant_pointer_abstract_pointert other) const
{
  if(is_bottom())
  {
    return std::make_shared<constant_pointer_abstract_objectt>(*other);
  }
  else
  {
    bool matching_pointer =
      value_stack.to_expression() == other->value_stack.to_expression();

    if(matching_pointer)
    {
      return shared_from_this();
    }
    else
    {
      return pointer_abstract_objectt::merge(other);
    }
  }
}

exprt constant_pointer_abstract_objectt::to_constant() const
{
  if(is_top() || is_bottom())
  {
    return pointer_abstract_objectt::to_constant();
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
    pointer_abstract_objectt::output(out, ai, ns);
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
  if(is_top() || is_bottom() || value_stack.is_top_value())
  {
    return pointer_abstract_objectt::write_dereference(
      environment, ns, stack, new_value, merging_write);
  }
  else
  {
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
          abstract_objectt::merge(pointed_value, new_value);
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
    return std::dynamic_pointer_cast<const constant_pointer_abstract_objectt>(
      shared_from_this());
  }
}

void constant_pointer_abstract_objectt::get_statistics(
  abstract_object_statisticst &statistics,
  abstract_object_visitedt &visited,
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  pointer_abstract_objectt::get_statistics(statistics, visited, env, ns);
  // don't bother following nullptr
  if(!is_top() && !is_bottom() && !value_stack.is_top_value())
  {
    read_dereference(env, ns)->get_statistics(statistics, visited, env, ns);
  }
  statistics.objects_memory_usage += memory_sizet::from_bytes(sizeof(*this));
}
