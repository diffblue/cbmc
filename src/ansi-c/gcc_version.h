/*******************************************************************\

Module: gcc version numbering scheme

Author: Daniel Kroening

Date: May 2018

\*******************************************************************/

#ifndef CPROVER_GOTO_CC_GCC_VERSION_H
#define CPROVER_GOTO_CC_GCC_VERSION_H

#include <util/config.h>

#include <iosfwd>
#include <string>
#include <vector>

class gcc_versiont
{
public:
  unsigned v_major, v_minor, v_patchlevel;

  /// Determines the version of the compiler \p executable, and the C and C++
  /// standards that its preprocessor uses with the options
  /// \p standard_options (such as `-std=c90` or `-ansi`), or by default when
  /// there are none.
  void get(
    const std::string &executable,
    const std::vector<std::string> &standard_options = {});

  /// \return the C standard that the value \p stdc_version of
  ///   `__STDC_VERSION__` indicates: C89 when it is not defined (as for C90),
  ///   and the latest one that CBMC supports for any later standard
  static configt::ansi_ct::c_standardt
  c_standard(const std::string &stdc_version);

  /// \return the C++ standard that the value \p cplusplus of `__cplusplus`
  ///   indicates, which is the latest one that CBMC supports for any later
  ///   standard
  static configt::cppt::cpp_standardt
  cpp_standard(const std::string &cplusplus);

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

  /// the standards that the preprocessor uses (see \ref get)
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
