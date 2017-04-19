/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cassert>

#include <cegis/cegis-util/string_helper.h>

bool contains(const std::string &haystack, const std::string &needle)
{
  return std::string::npos != haystack.find(needle);
}

bool starts_with(const std::string &haystack, const std::string &prefix)
{
  return haystack.substr(0, prefix.size()) == prefix;
}

bool ends_with(const std::string &haystack, const std::string &suffix)
{
  const std::string::size_type haystack_sz=haystack.size();
  const std::string::size_type suffix_sz=suffix.size();
  if(haystack_sz < suffix_sz) return false;
  return haystack.substr(haystack_sz - suffix_sz) == suffix;
}

void remove_suffix(std::string &haystack, const std::string &suffix)
{
  assert(ends_with(haystack, suffix));
  const size_t new_size=haystack.size() - suffix.size();
  haystack=haystack.substr(0, new_size);
}
