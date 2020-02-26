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
structured_data_entryt structured_data_entryt::data_node(const jsont &data)
{
  // Structured data (e.g. arrays and objects) should use an entry
  PRECONDITION(!(data.is_array() || data.is_object()));
  return structured_data_entryt(data);
}
structured_data_entryt
structured_data_entryt::entry(std::map<labelt, structured_data_entryt> children)
{
  return structured_data_entryt(children);
}
structured_data_entryt::structured_data_entryt(const jsont &data) : data(data)
{
}
structured_data_entryt::structured_data_entryt(
  std::map<labelt, structured_data_entryt> children)
  : children(std::move(children))
{
}
bool structured_data_entryt::is_leaf() const
{
  return children.empty();
}
std::string structured_data_entryt::leaf_data() const
{
  return data.value;
}
std::map<labelt, structured_data_entryt>
structured_data_entryt::get_children() const
{
  return children;
}
jsont structured_data_entryt::leaf_object() const
{
  return data;
}
structured_datat::structured_datat(
  std::map<labelt, structured_data_entryt> data)
  : data(std::move(data))
{
}

xmlt xml_node(const std::pair<labelt, structured_data_entryt> &entry)
{
  const labelt &label = entry.first;
  const structured_data_entryt &data = entry.second;
  xmlt output_data{label.kebab_case()};
  if(data.is_leaf())
  {
    output_data.data = data.leaf_data();
  }
  else
  {
    const auto &children = data.get_children();
    output_data.elements =
      make_range(children).map(xml_node).collect<std::list<xmlt>>();
  }
  return output_data;
}

xmlt structured_datat::to_xml() const
{
  if(data.size() == 0)
    return xmlt{};
  if(data.size() == 1)
  {
    return xml_node(*data.begin());
  }
  else
  {
    xmlt root{"root"};
    root.elements = make_range(data).map(xml_node).collect<std::list<xmlt>>();
    return root;
  }
}

jsont json_node(const structured_data_entryt &entry)
{
  if(entry.is_leaf())
    return entry.leaf_object();
  else
  {
    json_objectt result;
    for(const auto sub_entry : entry.get_children())
    {
      result[sub_entry.first.camel_case()] = json_node(sub_entry.second);
    }
    return std::move(result);
  }
}

jsont structured_datat::to_json() const
{
  if(data.size() == 0)
    return jsont{};

  json_objectt result;
  for(const auto sub_entry : data)
  {
    result[sub_entry.first.camel_case()] = json_node(sub_entry.second);
  }
  return std::move(result);
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
    const auto indent = [](const std::string line) { return "\t" + line; };

    const auto &children = data.get_children();
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

std::string structured_datat::to_pretty() const
{
  if(data.empty())
    return "";

  std::vector<std::vector<std::string>> lines =
    make_range(data)
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
