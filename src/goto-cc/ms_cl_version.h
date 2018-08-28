/*******************************************************************\

Module: Visual Studio CL version numbering scheme

Author: Daniel Kroening

Date: August 2018

\*******************************************************************/

#ifndef CPROVER_GOTO_CC_MS_CL_VERSION_H
#define CPROVER_GOTO_CC_MS_CL_VERSION_H

#include <iosfwd>
#include <string>

#include <util/config.h>

class ms_cl_versiont
{
public:
  unsigned v_major, v_minor;

  void get(const std::string &executable);

  bool is_at_least(unsigned v_major, unsigned v_minor = 0) const;

  configt::ansi_ct::c_standardt default_c_standard;
  configt::cppt::cpp_standardt default_cxx_standard;

  ms_cl_versiont()
    : v_major(0),
      v_minor(0),
      default_c_standard(configt::ansi_ct::c_standardt::C89),
      default_cxx_standard(configt::cppt::cpp_standardt::CPP98)
  {
  }

  enum class targett
  {
    UNKNOWN,
    x86,
    x64,
    ARM
  } target;
};

std::ostream &operator<<(std::ostream &, const ms_cl_versiont &);

#endif // CPROVER_GOTO_CC_MS_CL_VERSION_H
