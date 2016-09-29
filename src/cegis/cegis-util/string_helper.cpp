#include <cegis/cegis-util/string_helper.h>

bool contains(const std::string &haystack, const std::string &needle)
{
  return std::string::npos != haystack.find(needle);
}
