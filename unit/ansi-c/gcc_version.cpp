/*******************************************************************\

Module: Unit tests for gcc_versiont

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Unit tests for gcc_versiont

#include <ansi-c/gcc_version.h>
#include <testing-utils/use_catch.h>

TEST_CASE(
  "gcc_versiont maps __STDC_VERSION__ to a C standard",
  "[core][ansi-c][gcc_version]")
{
  using c_standardt = configt::ansi_ct::c_standardt;

  // C90 does not define __STDC_VERSION__, which then remains unexpanded
  CHECK(gcc_versiont::c_standard("__STDC_VERSION__") == c_standardt::C89);
  CHECK(gcc_versiont::c_standard("199409L") == c_standardt::C89);
  CHECK(gcc_versiont::c_standard("199901L") == c_standardt::C99);
  CHECK(gcc_versiont::c_standard("201112L") == c_standardt::C11);
  CHECK(gcc_versiont::c_standard("201710L") == c_standardt::C17);
  // -std=c2x with GCC 9 to 14, C23, and C2y with GCC 15
  CHECK(gcc_versiont::c_standard("202000L") == c_standardt::C23);
  CHECK(gcc_versiont::c_standard("202311L") == c_standardt::C23);
  CHECK(gcc_versiont::c_standard("202500L") == c_standardt::C23);
}

TEST_CASE(
  "gcc_versiont maps __cplusplus to a C++ standard",
  "[core][ansi-c][gcc_version]")
{
  using cpp_standardt = configt::cppt::cpp_standardt;

  CHECK(gcc_versiont::cpp_standard("199711L") == cpp_standardt::CPP98);
  CHECK(gcc_versiont::cpp_standard("201103L") == cpp_standardt::CPP11);
  CHECK(gcc_versiont::cpp_standard("201402L") == cpp_standardt::CPP14);
  CHECK(gcc_versiont::cpp_standard("201703L") == cpp_standardt::CPP17);
  // C++20, the default of GCC 16, and C++23
  CHECK(gcc_versiont::cpp_standard("202002L") == cpp_standardt::CPP17);
  CHECK(gcc_versiont::cpp_standard("202302L") == cpp_standardt::CPP17);
}
