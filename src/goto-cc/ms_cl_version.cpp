/*******************************************************************\

Module: Visual Studio CL version numbering scheme

Author: Daniel Kroening, 2018

\*******************************************************************/

#include "ms_cl_version.h"

#include <util/run.h>
#include <util/string2int.h>
#include <util/string_utils.h>
#include <util/tempfile.h>

#include <fstream>

void ms_cl_versiont::get(const std::string &executable)
{
  // stdout will have the help output, we just want to discard it
  temporary_filet tmp_file_out("goto-cl.", ".out");
  // stderr has the version string
  temporary_filet tmp_file_err("goto-cl.", ".err");
  const int result =
    run(executable, {executable}, "", tmp_file_out(), tmp_file_err());

  v_major = v_minor = 0;
  target = targett::UNKNOWN;

  if(result >= 0)
  {
    std::ifstream in(tmp_file_err());
    std::string line;

    if(std::getline(in, line))
    {
      // Example:
      //
      // NOLINTNEXTLINE (whitespace/braces)
      // Microsoft (R) 32-bit C/C++ Optimizing Compiler Version 15.00.30729.01 for 80x86
      auto split = split_string(line, ' ');
      if(split.size() > 3)
      {
        if(split.back() == "x86" || split.back() == "80x86")
          target = targett::x86;
        else if(split.back() == "x64")
          target = targett::x64;
        else if(split.back() == "ARM")
          target = targett::ARM;
        else
          target = targett::UNKNOWN;

        auto split_v = split_string(split[split.size() - 3], '.');

        if(split_v.size() >= 2)
        {
          v_major = safe_string2unsigned(split_v[0]);
          v_minor = safe_string2unsigned(split_v[1]);
        }
      }
    }
  }
}

bool ms_cl_versiont::is_at_least(unsigned _major, unsigned _minor) const
{
  return v_major > _major || (v_major == _major && v_minor >= _minor);
}

std::ostream &operator<<(std::ostream &out, const ms_cl_versiont &v)
{
  out << v.v_major << '.' << v.v_minor;

  switch(v.target)
  {
  case ms_cl_versiont::targett::x86:
    out << " x86";
    break;
  case ms_cl_versiont::targett::x64:
    out << " x64";
    break;
  case ms_cl_versiont::targett::ARM:
    out << " ARM";
    break;
  case ms_cl_versiont::targett::UNKNOWN:
    break;
  }

  return out;
}
