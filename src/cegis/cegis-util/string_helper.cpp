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
  if (haystack_sz < suffix_sz) return false;
  return haystack.substr(haystack_sz - suffix_sz) == suffix;
}
