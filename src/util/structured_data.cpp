/*******************************************************************\

Module: Classes for representing generic structured data

Author: Thomas Kiley

\*******************************************************************/

#include "structured_data.h"
#include "range.h"
#include "string_utils.h"
#include <algorithm>

labelt::labelt(std::vector<std::string> components) : components(components)
{
  PRECONDITION(!components.empty());
  PRECONDITION(std::all_of(
    components.begin(), components.end(), [](const std::string &component) {
      return !component.empty() &&
             std::none_of(component.begin(), component.end(), ::isupper);
    }));
}

std::string labelt::camel_case() const
{
  std::ostringstream output;
  output << *components.begin();
  join_strings(
    output, std::next(components.begin()), components.end(), "", capitalize);
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
  const auto range =
    make_range(components.begin(), std::next(components.begin()))
      .map(capitalize)
      .concat(make_range(std::next(components.begin()), components.end()));

  join_strings(output, range.begin(), range.end(), ' ');
  return output.str();
}

bool labelt::operator<(const labelt &other) const
{
  return components < other.components;
}

structured_data_entryt structured_data_entryt::data_node(const jsont &data)
{
  // Structured data (e.g. arrays and objects) should use an entry
  PRECONDITION(!(data.is_array() || data.is_object()));
  return structured_data_entryt(data);
}

structured_data_entryt
structured_data_entryt::entry(std::map<labelt, structured_data_entryt> children)
{
  return structured_data_entryt(std::move(children));
}

structured_data_entryt::structured_data_entryt(jsont data)
  : data(std::move(data))
{
}

structured_data_entryt::structured_data_entryt(
  std::map<labelt, structured_data_entryt> children)
  : _children(std::move(children))
{
}

bool structured_data_entryt::is_leaf() const
{
  return _children.empty();
}

std::string structured_data_entryt::leaf_data() const
{
  return data.value;
}
const std::map<labelt, structured_data_entryt> &
structured_data_entryt::children() const
{
  return _children;
}

jsont structured_data_entryt::leaf_object() const
{
  return data;
}

structured_datat::structured_datat(
  std::map<labelt, structured_data_entryt> data)
  : _data(std::move(data))
{
}

std::vector<std::string>
pretty_node(const std::pair<labelt, structured_data_entryt> &entry)
{
  const labelt &label = entry.first;
  const structured_data_entryt &data = entry.second;
  if(data.is_leaf())
  {
    std::ostringstream line;
    line << label.pretty() << ": " << data.leaf_data();
    return {line.str()};
  }
  else
  {
    const auto indent = [](const std::string &line) { return "\t" + line; };

    const auto &children = data.children();
    std::vector<std::vector<std::string>> lines =
      make_range(children)
        .map(pretty_node)
        .map([&](std::vector<std::string> sub_lines) {
          return make_range(sub_lines)
            .map(indent)
            .collect<std::vector<std::string>>();
        })
        .collect<std::vector<std::vector<std::string>>>();

    std::vector<std::string> result;
    for(const auto &sub_lines : lines)
    {
      result.insert(result.end(), sub_lines.begin(), sub_lines.end());
    }
    return result;
  }
}

std::string to_pretty(const structured_datat &data)
{
  if(data.data().empty())
    return "";

  std::vector<std::vector<std::string>> lines =
    make_range(data.data())
      .map(pretty_node)
      .collect<std::vector<std::vector<std::string>>>();
  std::vector<std::string> flattened_lines;
  for(const auto &line_section : lines)
  {
    flattened_lines.insert(
      flattened_lines.end(), line_section.begin(), line_section.end());
  }
  std::ostringstream output;
  join_strings(output, flattened_lines.begin(), flattened_lines.end(), "\n");
  return output.str();
}

const std::map<labelt, structured_data_entryt> &structured_datat::data() const
{
  return _data;
}
