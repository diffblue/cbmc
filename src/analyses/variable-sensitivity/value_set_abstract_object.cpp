/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: diffblue

\*******************************************************************/

/// \file
/// Value Set Abstract Object

#include <analyses/variable-sensitivity/array_abstract_object.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/constant_pointer_abstract_object.h>
#include <analyses/variable-sensitivity/context_abstract_object.h>
#include <analyses/variable-sensitivity/interval_abstract_value.h>
#include <analyses/variable-sensitivity/struct_abstract_object.h>
#include <analyses/variable-sensitivity/union_abstract_object.h>
#include <analyses/variable-sensitivity/value_set_abstract_object.h>

#include <langapi/language_util.h>

value_set_abstract_objectt::value_set_abstract_objectt(const typet &type)
  : abstract_valuet(type)
{
  verify();
}

value_set_abstract_objectt::value_set_abstract_objectt(
  const typet &type,
  bool top,
  bool bottom)
  : abstract_valuet(type, top, bottom)
{
  verify();
}

value_set_abstract_objectt::value_set_abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_valuet(expr.type(), false, false), values{expr}
{
  verify();
}

value_set_abstract_objectt::value_set_abstract_objectt(const typet &type, value_sett values)
  : abstract_valuet(type, false, values.empty()), values{std::move(values)}
{

}

namespace detail {
  template<typename Collection, typename Function>
  void generalized_cartesian_product_impl(const std::vector<Collection> &collections, std::vector<typename Collection::value_type>& arguments_so_far, Function&& function) {
    auto const collection_index = arguments_so_far.size();
    if(collection_index == collections.size()) {
      function(arguments_so_far);
    } else {
      for(auto element : collections[collection_index]) {
        arguments_so_far.push_back(element);
        generalized_cartesian_product_impl(collections, arguments_so_far, function);
        arguments_so_far.pop_back();
      }
    }
  }
}

template<typename Collection, typename Function>
void generalized_cartesian_product(const std::vector<Collection> &collections, Function&& function) {
  auto arguments_so_far = std::vector<typename Collection::value_type>{};
  detail::generalized_cartesian_product_impl(collections, arguments_so_far, function);
}

#include <type_traits>

abstract_object_pointert value_set_abstract_objectt::expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  std::size_t num_operands = expr.operands().size();
  PRECONDITION(operands.size() == num_operands);

  std::vector<value_sett> collective_operands;
  collective_operands.reserve(num_operands);
  for(const auto &op : operands)
  {
    auto vsab = std::dynamic_pointer_cast<const value_set_abstract_objectt>(
      maybe_unwrap_context(op));
    if(vsab->is_top()) {
      return make_top();
    }
    if(vsab->is_bottom()) {
      return make_bottom();
    }
    INVARIANT(vsab, "should be a value set abstract object");
    collective_operands.push_back(vsab->get_values());
  }

  value_sett resulting_values;
  generalized_cartesian_product(collective_operands, [&resulting_values, expr, ns](const std::vector<exprt>& operands) {
    exprt expr_instance = expr;
    expr_instance.operands() = operands;
    simplify(expr_instance, ns);
    resulting_values.insert(expr_instance);
  });

  if(resulting_values.size() > max_value_set_size) {
    return make_top();
  }
  return std::make_shared<value_set_abstract_objectt>(type(), resulting_values);
}

abstract_object_pointert
value_set_abstract_objectt::merge(abstract_object_pointert other) const
{
  auto cast_other =
    std::dynamic_pointer_cast<const value_set_abstract_objectt>(other);
  if(cast_other != nullptr)
  {
    auto union_values = values;
    union_values.insert(
      cast_other->get_values().begin(), cast_other->get_values().end());
    return std::make_shared<value_set_abstract_objectt>(type(), union_values);
  }
  else
    return abstract_objectt::merge(other);
}

abstract_object_pointert value_set_abstract_objectt::maybe_unwrap_context(
  const abstract_object_pointert &maybe_wrapped)
{
  auto const &context_value =
    std::dynamic_pointer_cast<const context_abstract_objectt>(maybe_wrapped);

  return context_value ? context_value->unwrap_context() : maybe_wrapped;
}

void value_set_abstract_objectt::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  if(is_top())
  {
    out << "TOP";
  }
  else if(is_bottom())
  {
    out << "BOTTOM";
  }
  else
  {
    out << "value_set{";
    for(auto const &value : values)
    {
      out << from_expr(value) <<  ", ";
    }
    out << "}";
  }
}
