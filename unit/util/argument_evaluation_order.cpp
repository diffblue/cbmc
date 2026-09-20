/*******************************************************************\

Module: Unit test for configt::ansi_ct::argument_evaluation_order

Author: Michael Tautschnig

\*******************************************************************/

#include <util/config.h>

#include <testing-utils/config_restore.h>
#include <testing-utils/use_catch.h>

TEST_CASE(
  "argument evaluation order per architecture and compiler",
  "[core][util][config]")
{
  config_restoret restore_config;

  using aeot = configt::ansi_ct::argument_evaluation_ordert;

  SECTION("GCC evaluates right-to-left on the x86 family")
  {
    config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
    for(auto arch : {"i386", "x86_64", "x32"})
    {
      config.set_arch(arch);
      REQUIRE(config.ansi_c.argument_evaluation_order == aeot::RIGHT_TO_LEFT);
    }
  }

  SECTION("Visual Studio evaluates right-to-left on all architectures")
  {
    config.ansi_c.mode = configt::ansi_ct::flavourt::VISUAL_STUDIO;
    for(auto arch : {"i386", "x86_64", "arm64", "arm"})
    {
      config.set_arch(arch);
      REQUIRE(config.ansi_c.argument_evaluation_order == aeot::RIGHT_TO_LEFT);
    }
  }

  SECTION("Clang evaluates left-to-right on all architectures")
  {
    config.ansi_c.mode = configt::ansi_ct::flavourt::CLANG;
    for(auto arch : {"i386", "x86_64", "x32", "arm64", "riscv64"})
    {
      config.set_arch(arch);
      REQUIRE(config.ansi_c.argument_evaluation_order == aeot::LEFT_TO_RIGHT);
    }
  }

  SECTION("GCC evaluates left-to-right on non-x86 architectures")
  {
    config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
    for(auto arch :
        {"arm64",
         "arm",
         "armhf",
         "riscv64",
         "ppc64le",
         "mips64el",
         "s390x",
         "sparc64"})
    {
      config.set_arch(arch);
      REQUIRE(config.ansi_c.argument_evaluation_order == aeot::LEFT_TO_RIGHT);
    }
  }
}
