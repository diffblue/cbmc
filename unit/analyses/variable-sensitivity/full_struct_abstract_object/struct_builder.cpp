/*******************************************************************\

 Module: Unit tests helpers for structs

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/
#include <analyses/variable-sensitivity/full_struct_abstract_object/struct_builder.h>
#include <util/arith_tools.h>
#include <util/mathematical_types.h>

full_struct_abstract_objectt::constant_struct_pointert build_struct(
  const struct_exprt &starting_value,
  abstract_environmentt &environment,
  const namespacet &ns)
{
  auto result = std::make_shared<const full_struct_abstract_objectt>(
    starting_value, environment, ns);

  auto struct_type = to_struct_type(starting_value.type());
  size_t comp_index = 0;

  auto nil_with_type = nil_exprt();
  nil_with_type.type() = struct_type;

  for(const exprt &op : starting_value.operands())
  {
    const auto &component = struct_type.components()[comp_index];
    auto new_result = result->write(
      environment,
      ns,
      std::stack<exprt>(),
      member_exprt(nil_with_type, component.get_name(), component.type()),
      environment.eval(op, ns),
      false);

    result =
      std::dynamic_pointer_cast<const full_struct_abstract_objectt>(new_result);

    ++comp_index;
  }

  return result;
}

full_struct_abstract_objectt::constant_struct_pointert build_struct(
  const std::map<std::string, int> &members,
  abstract_environmentt &environment,
  const namespacet &ns)
{
  struct_typet struct_type;
  exprt::operandst val1_op;

  for(auto &member : members)
  {
    auto component =
      struct_union_typet::componentt(member.first, integer_typet());
    struct_type.components().push_back(component);

    if(member.second != TOP_MEMBER)
      val1_op.push_back(from_integer(member.second, integer_typet()));
    else
      val1_op.push_back(nil_exprt());
  }

  auto val1 = struct_exprt(val1_op, struct_type);
  return build_struct(val1, environment, ns);
}

full_struct_abstract_objectt::constant_struct_pointert build_top_struct()
{
  struct_typet struct_type;
  return std::make_shared<full_struct_abstract_objectt>(
    struct_type, true, false);
}

full_struct_abstract_objectt::constant_struct_pointert build_bottom_struct()
{
  struct_typet struct_type;
  return std::make_shared<full_struct_abstract_objectt>(
    struct_type, false, true);
}

exprt read_component(
  full_struct_abstract_objectt::constant_struct_pointert struct_object,
  const member_exprt &component,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  return struct_object->expression_transform(component, {}, environment, ns)
    ->to_constant();
}
