/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Jez Higgins

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/two_value_pointer_abstract_object.h>

#include <util/pointer_expr.h>

two_value_pointer_abstract_objectt::two_value_pointer_abstract_objectt(
  const typet &type)
  : abstract_pointer_objectt(type)
{
}

two_value_pointer_abstract_objectt::two_value_pointer_abstract_objectt(
  const typet &type,
  bool top,
  bool bottom)
  : abstract_pointer_objectt(type, top, bottom)
{
}

two_value_pointer_abstract_objectt::two_value_pointer_abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_pointer_objectt(expr, environment, ns)
{
}

abstract_object_pointert two_value_pointer_abstract_objectt::read_dereference(
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  pointer_typet pointer_type(to_pointer_type(type()));
  const typet &pointed_to_type = pointer_type.base_type();

  return env.abstract_object_factory(pointed_to_type, ns, true, false);
}

abstract_object_pointert two_value_pointer_abstract_objectt::write_dereference(
  abstract_environmentt &env,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  if(is_top() || is_bottom())
  {
    env.havoc("Writing to a 2value pointer");
    return shared_from_this();
  }

  return std::make_shared<two_value_pointer_abstract_objectt>(
    type(), true, false);
}

abstract_object_pointert two_value_pointer_abstract_objectt::typecast(
  const typet &new_type,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  INVARIANT(is_void_pointer(type()), "Only allow pointer casting from void*");
  return std::make_shared<two_value_pointer_abstract_objectt>(
    new_type, is_top(), is_bottom());
}

abstract_object_pointert two_value_pointer_abstract_objectt::ptr_diff(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  return environment.eval(nil_exprt(), ns);
}

exprt two_value_pointer_abstract_objectt::ptr_comparison_expr(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  return nil_exprt();
}
