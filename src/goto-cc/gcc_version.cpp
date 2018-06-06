/*******************************************************************\

Module: GCC Mode

Author: Daniel Kroening, 2018

\*******************************************************************/

#include "gcc_version.h"

#include <util/prefix.h>
#include <util/run.h>
#include <util/string2int.h>
#include <util/string_utils.h>
#include <util/tempfile.h>

#include <fstream>

void gcc_versiont::get(const std::string &executable)
{
  temporary_filet tmp_file_in("goto-gcc.", ".in");
  temporary_filet tmp_file_out("goto-gcc.", ".out");
  temporary_filet tmp_file_err("goto-gcc.", ".err");

  {
    std::ofstream out(tmp_file_in());

    out << "#if defined(__clang_major__)\n"
           "clang __clang_major__ __clang_minor__ __clang_patchlevel__\n"
           "#elif defined(__BCC__)\n"
           "bcc 0 0 0\n"
           "#else\n"
           "gcc __GNUC__ __GNUC_MINOR__ __GNUC_PATCHLEVEL__\n"
           "#endif\n";
  }

  // some variants output stuff on stderr, say Apple LLVM,
  // which we silence.
  int result = run(
    executable,
    {executable, "-E", "-", "-o", "-"},
    tmp_file_in(),
    tmp_file_out(),
    tmp_file_err());

  v_major = v_minor = v_patchlevel = 0;
  flavor = flavort::UNKNOWN;

  if(result >= 0)
  {
    std::ifstream in(tmp_file_out());
    std::string line;

    while(!in.fail() && std::getline(in, line))
      if(!line.empty() && line[0] != '#')
        break;

    auto split = split_string(line, ' ');

    if(split.size() >= 4)
    {
      if(split[0] == "gcc")
        flavor = flavort::GCC;
      else if(split[0] == "bcc")
        flavor = flavort::BCC;
      else if(split[0] == "clang")
        flavor = flavort::CLANG;

      v_major = unsafe_string2unsigned(split[1]);
      v_minor = unsafe_string2unsigned(split[2]);
      v_patchlevel = unsafe_string2unsigned(split[3]);
    }
  }
}

bool gcc_versiont::is_at_least(
  unsigned _major,
  unsigned _minor,
  unsigned _patchlevel) const
{
  return v_major > _major || (v_major == _major && v_minor > _minor) ||
         (v_major == _major && v_minor == _minor &&
          v_patchlevel >= _patchlevel);
}

std::ostream &operator<<(std::ostream &out, const gcc_versiont &v)
{
  return out << v.v_major << '.' << v.v_minor << '.' << v.v_patchlevel;
}
