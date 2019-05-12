/*******************************************************************\

Module: gcc version numbering scheme

Author: Daniel Kroening

Date: May 2018

\*******************************************************************/

#ifndef CPROVER_GOTO_CC_GCC_VERSION_H
#define CPROVER_GOTO_CC_GCC_VERSION_H

#include <iosfwd>
#include <string>

#include <util/config.h>

class gcc_versiont
{
public:
  unsigned v_major, v_minor, v_patchlevel;

  void get(const std::string &executable);

  bool is_at_least(
    unsigned v_major,
    unsigned v_minor = 0,
    unsigned v_patchlevel = 0) const;

  enum class flavort
  {
    UNKNOWN,
    CLANG,
    GCC,
    BCC
  } flavor;

  configt::ansi_ct::c_standardt default_c_standard;
  configt::cppt::cpp_standardt default_cxx_standard;

  gcc_versiont()
    : v_major(0),
      v_minor(0),
      v_patchlevel(0),
      flavor(flavort::UNKNOWN),
      default_c_standard(configt::ansi_ct::c_standardt::C89),
      default_cxx_standard(configt::cppt::cpp_standardt::CPP98)
  {
  }
};

void configure_gcc(const gcc_versiont &);

std::ostream &operator<<(std::ostream &, const gcc_versiont &);

#endif
