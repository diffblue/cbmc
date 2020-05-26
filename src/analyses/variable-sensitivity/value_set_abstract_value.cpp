/*******************************************************************\

 Module: analyses variable-sensitivity variable-sensitivity-value-set

 Author: Diffblue Ltd.

\*******************************************************************/

#include "value_set_abstract_value.h"

value_set_abstract_valuet::value_set_abstract_valuet(const typet &type)
  : abstract_valuet{type}, values{}
{
}

const value_set_abstract_valuet::valuest &
value_set_abstract_valuet::get_values() const
{
  PRECONDITION(!is_top());
  PRECONDITION(!is_bottom());
  return values;
}

abstract_object_pointert
value_set_abstract_valuet::merge(abstract_object_pointert other) const
{
  if(is_top())
  {
    return shared_from_this();
  }

  if(other->is_top())
  {
    return other;
  }

  if(is_bottom())
  {
    return other;
  }

  if(other->is_bottom())
  {
    return shared_from_this();
  }

  if(
    auto other_value_set =
      dynamic_cast<const value_set_abstract_valuet *>(other.get()))
  {
    valuest merged_values{values};
    auto const &other_values = other_value_set->get_values();
    merged_values.insert(other_values.begin(), other_values.end());
    return std::make_shared<value_set_abstract_valuet>(
      type(), std::move(merged_values));
  }
  return abstract_objectt::merge(other);
}

value_set_abstract_valuet::value_set_abstract_valuet(
  const typet &type,
  valuest values)
  : abstract_valuet{type, values.size() > max_value_set_size, values.empty()},
    values{std::move(values)}
{
  if(values.size() > max_value_set_size)
  {
    this->values.clear();
  }
}

value_set_abstract_valuet::value_set_abstract_valuet(
  exprt expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : value_set_abstract_valuet{expr.type(), valuest{expr}}
{
}
