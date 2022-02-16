/*******************************************************************\

Module: C Defines

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// c_defines

#include "c_defines.h"

#include "cscanner.h"

#include <util/prefix.h>
#include <util/string_utils.h>

#include <sstream>

void c_definest::parse(const std::string &src)
{
  const auto lines = split_string(src, '\n');
  for(const auto &line : lines)
  {
    // #define __x86_64__ 1
    // #define getc_unlocked(fp) __sgetc(fp)
    if(!has_prefix(line, "#define "))
      continue;

    auto space_pos = line.find(' ', 8);
    if(space_pos == std::string::npos)
      continue;

    auto id = line.substr(8, space_pos - 8);
    auto value = line.substr(space_pos + 1, std::string::npos);
    map[id].value = value;
  }
}

std::string c_definest::operator()(const std::string &src) const
{
  // tokenize
  std::istringstream in(src);
  cscannert cscanner(in);
  const auto tokens = cscanner.get_tokens();

  // output
  std::ostringstream out;
  for(auto &t : tokens)
  {
    if(is_identifier(t))
    {
      auto m_it = map.find(t.text);
      if(m_it != map.end())
      {
        out << m_it->second.value;
      }
      else
        out << t.text;
    }
    else
      out << t.text;
  }

  return out.str();
}
