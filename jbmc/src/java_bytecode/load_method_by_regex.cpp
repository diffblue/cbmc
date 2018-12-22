
/*******************************************************************\

Module: Java Bytecode

Author: Diffblue Ltd.

\*******************************************************************/

#include "load_method_by_regex.h"

#include <regex>

#include <util/symbol_table.h>

/// For a given user provided pattern, return a regex, having dealt with the
/// cases where the user has not prefixed with java:: or suffixed with the
/// descriptor
/// \param pattern: The user provided pattern
/// \return The regex to match with
static std::regex build_regex_from_pattern(const std::string &pattern)
{
  std::string modified_pattern = pattern;
  if(does_pattern_miss_descriptor(pattern))
    modified_pattern += R"(:\(.*\).*)";

  if(!has_prefix(pattern, "java::"))
    modified_pattern = "java::" + modified_pattern;

  return std::regex{modified_pattern};
}

/// Identify if a parameter includes a part that will match a descriptor. That
/// is, does it have a colon separtor.
/// \param pattern: The user provided pattern
/// \return True if no descriptor is found (that is, the only : relates to the
///   java:: prefix.
bool does_pattern_miss_descriptor(const std::string &pattern)
{
  const size_t descriptor_index = pattern.rfind(':');
  if(descriptor_index == std::string::npos)
    return true;

  const std::string java_prefix = "java::";
  return descriptor_index == java_prefix.length() - 1 &&
         has_prefix(pattern, java_prefix);
}

/// Create a lambda that returns the symbols that the given pattern should be
/// loaded.If the pattern doesn't include a colon for matching the descriptor,
/// append a :\(.*\).* to the regex. Note this will mean all overloaded
/// methods will be marked as extra entry points for CI lazy loading.
/// If the pattern doesn't include the java:: prefix, prefix that
/// \param pattern: The user provided pattern
/// \return The lambda to execute.
std::function<std::vector<irep_idt>(const symbol_tablet &symbol_table)>
build_load_method_by_regex(const std::string &pattern)
{
  std::regex regex = build_regex_from_pattern(pattern);

  return [=](const symbol_tablet &symbol_table) {
    std::vector<irep_idt> matched_methods;
    for(const auto &symbol : symbol_table.symbols)
    {
      if(
        symbol.second.is_function() &&
        std::regex_match(id2string(symbol.first), regex))
      {
        matched_methods.push_back(symbol.first);
      }
    }
    return matched_methods;
  };
}
