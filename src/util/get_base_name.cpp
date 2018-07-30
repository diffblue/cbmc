/*******************************************************************\

Module:

Author: CM Wintersteiger

Date:

\*******************************************************************/

#include "get_base_name.h"

/// cleans a filename from path and extension
/// \par parameters: a string
/// \return a new string
std::string get_base_name(const std::string &in, bool strip_suffix)
{
#ifdef _WIN32
  // Windows now allows both '/' and '\\'
  const std::size_t slash_pos = in.find_last_of("\\/");
#else
  const std::size_t slash_pos = in.rfind('/');
#endif

  std::size_t start_pos;

  if(slash_pos == std::string::npos)
    start_pos = 0;
  else
    start_pos = slash_pos + 1;

  std::size_t char_count;

  if(strip_suffix)
  {
    std::size_t dot_pos = in.rfind('.');
    if(dot_pos == std::string::npos || dot_pos < start_pos)
      char_count = std::string::npos;
    else
      char_count = dot_pos - start_pos;
  }
  else
    char_count = std::string::npos;

  return std::string(in, start_pos, char_count);
}
