/*******************************************************************\

Module: Classes for representing generic structured data

Author: Thomas Kiley

\*******************************************************************/

#include "structured_data.h"
#include "range.h"
#include "string_utils.h"
#include <algorithm>

std::string capitalize(const std::string &str)
{
  std::string capitalized = str;
  capitalized[0] = toupper(capitalized[0]);
  return capitalized;
}

labelt::labelt(std::vector<std::string> components)
{
  auto to_lower_string = [](const std::string &s) -> std::string {
    std::string lower_case = s;
    std::for_each(
      lower_case.begin(), lower_case.end(), [](char &c) { c = ::tolower(c); });
    return lower_case;
  };
  this->components = make_range(components)
                       .map(to_lower_string)
                       .collect<std::vector<std::string>>();
}
std::string labelt::camel_case() const
{
  std::ostringstream output;
  if(!components.empty())
  {
    output << *components.begin();
    join_strings(
      output, std::next(components.begin()), components.end(), "", capitalize);
  }
  return output.str();
}
std::string labelt::snake_case() const
{
  std::ostringstream output;
  join_strings(output, components.begin(), components.end(), '_');
  return output.str();
}
std::string labelt::kebab_case() const
{
  std::ostringstream output;
  join_strings(output, components.begin(), components.end(), '-');
  return output.str();
}
std::string labelt::pretty() const
{
  std::ostringstream output;
  if(!components.empty())
  {
    const auto range =
      make_range(components.begin(), std::next(components.begin()))
        .map(capitalize)
        .concat(make_range(std::next(components.begin()), components.end()));

    join_strings(output, range.begin(), range.end(), ' ');
  }
  return output.str();
}
bool labelt::operator<(const labelt &other) const
{
  return camel_case() < other.camel_case();
}
