/*******************************************************************\

Module: gcc version numbering scheme

Author: Daniel Kroening

Date: May 2018

\*******************************************************************/

#ifndef CPROVER_GOTO_CC_GCC_VERSION_H
#define CPROVER_GOTO_CC_GCC_VERSION_H

#include <iosfwd>
#include <string>

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

  gcc_versiont()
    : v_major(0), v_minor(0), v_patchlevel(0), flavor(flavort::UNKNOWN)
  {
  }
};

std::ostream &operator<<(std::ostream &, const gcc_versiont &);

#endif
