/*******************************************************************\

 Module: Unit tests helpers for arrays

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/full_array_abstract_object.h>
#include <analyses/variable-sensitivity/full_array_abstract_object/array_builder.h>
#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>

full_array_abstract_objectt::full_array_pointert build_array(
  const exprt &array_expr,
  abstract_environmentt &environment,
  const namespacet &ns)
{
  return std::make_shared<full_array_abstract_objectt>(
    array_expr, environment, ns);
}

full_array_abstract_objectt::full_array_pointert build_array(
  const std::vector<int> &array,
  abstract_environmentt &environment,
  const namespacet &ns)
{
  const typet type = signedbv_typet(32);

  const array_typet array_type(type, from_integer(array.size(), type));

  exprt::operandst element_ops;

  for(auto element : array)
  {
    if(element != TOP_MEMBER)
      element_ops.push_back(from_integer(element, type));
    else
      element_ops.push_back(nil_exprt());
  }

  auto array_expr = array_exprt(element_ops, array_type);
  return build_array(array_expr, environment, ns);
}

full_array_abstract_objectt::full_array_pointert build_top_array()
{
  auto array_type =
    array_typet(integer_typet(), from_integer(3, integer_typet()));
  return std::make_shared<full_array_abstract_objectt>(array_type, true, false);
}

full_array_abstract_objectt::full_array_pointert build_bottom_array()
{
  auto array_type =
    array_typet(integer_typet(), from_integer(3, integer_typet()));
  return std::make_shared<full_array_abstract_objectt>(array_type, false, true);
}
