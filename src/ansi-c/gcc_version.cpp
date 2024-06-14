/*******************************************************************\

Module: GCC Mode

Author: Daniel Kroening, 2018

\*******************************************************************/

#include "gcc_version.h"

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
           "#endif\n"
           "default_c_standard __STDC_VERSION__\n";
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
    {
      if(line.empty() || line[0] == '#')
        continue;

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
      else if(split.size() == 2 && split[0] == "default_c_standard")
      {
        if(split[1] == "199901L")
          default_c_standard = configt::ansi_ct::c_standardt::C99;
        else if(split[1] == "201112L")
          default_c_standard = configt::ansi_ct::c_standardt::C11;
      }
    }

    if(flavor == flavort::GCC || flavor == flavort::CLANG)
    {
      // Grab the default C++ standard. Unfortunately this requires another
      // run, as the compiler can't preprocess two files in one go.

      temporary_filet cpp_in("goto-gcc.", ".cpp");
      temporary_filet cpp_out("goto-gcc.", ".out");
      temporary_filet cpp_err("goto-gcc.", ".err");

      {
        std::ofstream out(cpp_in());
        out << "default_cxx_standard __cplusplus\n";
      }

      result = run(
        executable,
        {executable, "-E", "-x", "c++", "-", "-o", "-"},
        cpp_in(),
        cpp_out(),
        cpp_err());

      if(result >= 0)
      {
        std::ifstream in2(cpp_out());

        while(!in2.fail() && std::getline(in2, line))
        {
          if(line.empty() || line[0] == '#')
            continue;

          auto split = split_string(line, ' ');

          if(split.size() == 2 && split[0] == "default_cxx_standard")
          {
            if(split[1] == "199711L")
              default_cxx_standard = configt::cppt::cpp_standardt::CPP98;
            else if(split[1] == "201103L")
              default_cxx_standard = configt::cppt::cpp_standardt::CPP11;
            else if(split[1] == "201402L")
              default_cxx_standard = configt::cppt::cpp_standardt::CPP14;
            else if(split[1] == "201703L")
              default_cxx_standard = configt::cppt::cpp_standardt::CPP17;
          }
        }
      }
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

void configure_gcc(const gcc_versiont &gcc_version)
{
  // ISO/IEC TS 18661-3:2015 support was introduced with gcc 7.0
  if(
    gcc_version.flavor == gcc_versiont::flavort::GCC &&
    gcc_version.is_at_least(7u))
  {
    config.ansi_c.ts_18661_3_Floatn_types = true;
  }

  const auto gcc_float128_minor_version =
    config.ansi_c.arch == "x86_64" ? 3u : 5u;

  // __float128 exists (as a typedef) since gcc 4.5 everywhere,
  // and since 4.3 on x86_64
  config.ansi_c.gcc__float128_type =
    gcc_version.flavor == gcc_versiont::flavort::GCC &&
    gcc_version.is_at_least(4u, gcc_float128_minor_version);
  config.ansi_c.__float128_is_keyword =
    gcc_version.flavor == gcc_versiont::flavort::CLANG ||
    (gcc_version.flavor == gcc_versiont::flavort::GCC &&
     config.ansi_c.arch == "arm64" &&
     config.ansi_c.os == configt::ansi_ct::ost::OS_MACOS &&
     config.ansi_c.gcc__float128_type);

  config.ansi_c.float16_type =
    (gcc_version.flavor == gcc_versiont::flavort::GCC &&
     gcc_version.is_at_least(12u)) ||
    (gcc_version.flavor == gcc_versiont::flavort::CLANG &&
     gcc_version.is_at_least(15u));

  config.ansi_c.bf16_type =
    (gcc_version.flavor == gcc_versiont::flavort::GCC &&
     gcc_version.is_at_least(13u)) ||
    (gcc_version.flavor == gcc_versiont::flavort::CLANG &&
     gcc_version.is_at_least(15u));

  config.ansi_c.fp16_type =
    (gcc_version.flavor == gcc_versiont::flavort::GCC &&
     gcc_version.is_at_least(4u, 5u) &&
     (config.ansi_c.arch == "arm" || config.ansi_c.arch == "arm64")) ||
    (gcc_version.flavor == gcc_versiont::flavort::CLANG &&
     gcc_version.is_at_least(6u));
}
