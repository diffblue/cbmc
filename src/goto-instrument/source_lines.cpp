/*******************************************************************\

Module: Source Lines

Author: Mark R. Tuttle

\*******************************************************************/

/// \file
/// Set of source code lines contributing to a basic block

#include "source_lines.h"

#include <util/format_number_range.h>
#include <util/range.h>
#include <util/source_location.h>
#include <util/string2int.h>
#include <util/string_utils.h>

#include <sstream>

void source_linest::insert(const source_locationt &loc)
{
  if(loc.get_file().empty() || loc.is_built_in())
    return;
  const std::string &file = id2string(loc.get_file());

  // the function of a source location can fail to be set
  const std::string &func = id2string(loc.get_function());

  if(loc.get_line().empty())
    return;
  std::size_t line = safe_string2size_t(id2string(loc.get_line()));

  block_lines[file][func].insert(line);
}

std::string source_linest::to_string() const
{
  std::stringstream result;
  const auto full_map =
    make_range(block_lines)
      .map([&](const block_linest::value_type &file_entry) {
        std::stringstream ss;
        const auto map = make_range(file_entry.second)
                           .map([&](const function_linest::value_type &pair) {
                             std::vector<unsigned> line_numbers(
                               pair.second.begin(), pair.second.end());
                             return file_entry.first + ':' + pair.first + ':' +
                                    format_number_range(line_numbers);
                           });
        join_strings(ss, map.begin(), map.end(), "; ");
        return ss.str();
      });
  join_strings(result, full_map.begin(), full_map.end(), "; ");
  return result.str();
}

irept source_linest::to_irep() const
{
  irept result;

  for(const auto &file_entry : block_lines)
  {
    irept file_result;
    for(const auto &lines_entry : file_entry.second)
    {
      std::vector<unsigned> line_numbers(
        lines_entry.second.begin(), lines_entry.second.end());
      file_result.set(lines_entry.first, format_number_range(line_numbers));
    }
    result.add(file_entry.first, std::move(file_result));
  }

  return result;
}
