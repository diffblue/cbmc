/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_object_set.h>

#include <util/interval.h>
#include <util/string_utils.h>

#include <algorithm>

static bool by_length(const std::string &lhs, const std::string &rhs)
{
  if(lhs.size() < rhs.size())
    return true;
  if(lhs.size() > rhs.size())
    return false;
  return lhs < rhs;
}

void abstract_object_sett::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  std::vector<std::string> output_values;
  for(const auto &value : values)
  {
    std::ostringstream ss;
    value->output(ss, ai, ns);
    output_values.emplace_back(ss.str());
  }
  std::sort(output_values.begin(), output_values.end(), by_length);

  join_strings(out, output_values.begin(), output_values.end(), ", ");
}

constant_interval_exprt abstract_object_sett::to_interval() const
{
  PRECONDITION(!values.empty());

  auto initial =
    std::dynamic_pointer_cast<const abstract_value_objectt>(first())
      ->to_interval();

  if(initial.is_boolean() && values.size() == 2) // must be both true and false
    return constant_interval_exprt(false_exprt(), true_exprt());

  exprt lower_expr = initial.get_lower();
  exprt upper_expr = initial.get_upper();

  for(const auto &value : values)
  {
    const auto &v =
      std::dynamic_pointer_cast<const abstract_value_objectt>(value);
    const auto &value_expr = v->to_interval();
    lower_expr =
      constant_interval_exprt::get_min(lower_expr, value_expr.get_lower());
    upper_expr =
      constant_interval_exprt::get_max(upper_expr, value_expr.get_upper());
  }
  return constant_interval_exprt(lower_expr, upper_expr);
}
