/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_object_set.h>
#include <analyses/variable-sensitivity/interval_abstract_value.h>
#include <util/interval.h>
#include <util/string_utils.h>

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

  exprt lower_expr = first()->to_constant();
  exprt upper_expr = first()->to_constant();
  for(const auto &value : values)
  {
    const auto &value_expr = value->to_constant();
    lower_expr = constant_interval_exprt::get_min(lower_expr, value_expr);
    upper_expr = constant_interval_exprt::get_max(upper_expr, value_expr);
  }
  return constant_interval_exprt(lower_expr, upper_expr);
}
