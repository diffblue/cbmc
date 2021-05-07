/*******************************************************************\

Module: GOTO-CC Main Module

Authors: Daniel Kroening, kroening@kroening.com

Date: May 2006

\*******************************************************************/

/// \file
/// GOTO-CC Main Module

#include <algorithm>
#include <iostream>

#include <util/get_base_name.h>

#ifdef _MSC_VER
#  include <util/unicode.h>
#endif

#include "armcc_cmdline.h"
#include "as86_cmdline.h"
#include "as_cmdline.h"
#include "bcc_cmdline.h"
#include "gcc_cmdline.h"
#include "ld_cmdline.h"
#include "ms_cl_cmdline.h"
#include "ms_link_cmdline.h"

#include "armcc_mode.h"
#include "as_mode.h"
#include "cw_mode.h"
#include "gcc_mode.h"
#include "ld_mode.h"
#include "ms_cl_mode.h"
#include "ms_link_mode.h"

std::string to_lower_string(const std::string &s)
{
  std::string result=s;
  transform(result.begin(), result.end(), result.begin(), tolower);
  return result;
}

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
#else
int main(int argc, const char **argv)
#endif
{
  #ifdef _MSC_VER
  auto vec=narrow_argv(argc, argv_wide);
  auto narrow=to_c_str_array(std::begin(vec), std::end(vec));
  auto argv=narrow.data();
  #endif

  if(argv==nullptr || argc<1)
  {
    std::cerr << "failed to determine base name\n";
    return 1;
  }

  #ifdef _MSC_VER
  // we do 'to_lower_string' because of Windows
  std::string base_name=
    to_lower_string(get_base_name(argv[0], true));
  #else
  std::string base_name=get_base_name(argv[0], false);
  #endif

  if(base_name == "goto-cl" || base_name == "cl")
  {
    // this is the Visual Studio CL personality
    ms_cl_cmdlinet cmdline;
    cmdline.parse_env();
    ms_cl_modet ms_cl_mode(cmdline, base_name);
    return ms_cl_mode.main(argc, argv);
  }
  else if(base_name == "goto-link" || base_name == "link")
  {
    // this is the Visual Studio LINK personality
    ms_link_cmdlinet cmdline;
    ms_link_modet ms_link_mode(cmdline);
    return ms_link_mode.main(argc, argv);
  }
  else if(base_name=="goto-cw" ||
          base_name=="goto-cw-link")
  {
    // this is the CodeWarrior personality,
    // but we use the gcc command line interface
    gcc_cmdlinet cmdline;
    cw_modet cw_mode(cmdline, base_name);
    return cw_mode.main(argc, argv);
  }
  else if(base_name=="goto-armcc" ||
          base_name=="goto-armlink")
  {
    // this is the armcc personality
    armcc_cmdlinet cmdline;
    armcc_modet armcc_mode(cmdline, base_name);
    return armcc_mode.main(argc, argv);
  }
  // handle GCC names like x86_64-apple-darwin14-llvm-gcc-4.2
  // via x86_64-apple-darwin14-llvm-goto-gcc-4.2
  else if(base_name=="goto-clang" ||
          base_name.find("goto-gcc")!=std::string::npos)
  {
    // this produces ELF/Mach-O "hybrid binaries",
    // with a GCC-style command-line interface,
    // but also disables CPROVER language extensions
    gcc_cmdlinet cmdline;
    gcc_modet gcc_mode(cmdline, base_name, true);
    return gcc_mode.main(argc, argv);
  }
  else if(base_name.find("goto-ld")!=std::string::npos)
  {
    // this simulates "ld" for linking
    ld_cmdlinet cmdline;
    ld_modet ld_mode(cmdline, base_name);
    return ld_mode.main(argc, argv);
  }
  else if(base_name.find("goto-bcc")!=std::string::npos)
  {
    // this simulates Bruce's C Compiler
    bcc_cmdlinet cmdline;
    // bcc does not build ELF objects -- hybrid mode is used
    // with -S only
    gcc_modet gcc_mode(cmdline, base_name, true);
    return gcc_mode.main(argc, argv);
  }
  else if(base_name.find("goto-as86")!=std::string::npos)
  {
    // assembler used by Bruce's C Compiler
    as86_cmdlinet cmdline;
    // as86 does not build ELF objects, no hybrid binaries
    as_modet as_mode(cmdline, base_name, false);
    return as_mode.main(argc, argv);
  }
  else if(base_name.find("goto-as")!=std::string::npos)
  {
    // GNU assembler
    as_cmdlinet cmdline;
    as_modet as_mode(cmdline, base_name, true);
    return as_mode.main(argc, argv);
  }
  else
  {
    // the default personality is GCC-style
    gcc_cmdlinet cmdline;
    gcc_modet gcc_mode(cmdline, base_name, false);
    return gcc_mode.main(argc, argv);
  }
}
