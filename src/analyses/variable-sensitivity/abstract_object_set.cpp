/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_object_set.h>
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
