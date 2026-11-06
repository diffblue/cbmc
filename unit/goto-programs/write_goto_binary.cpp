/*******************************************************************\

Module: Unit tests for write_goto_binary

Author: Diffblue Ltd.

\*******************************************************************/

#include <util/message.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/write_goto_binary.h>

#include <testing-utils/use_catch.h>

#include <sstream>

TEST_CASE(
  "write_goto_binary validates the version before writing",
  "[core][goto-programs][write_goto_binary]")
{
  const goto_modelt goto_model;
  null_message_handlert message_handler;

  SECTION("a version below the supported one is rejected, nothing written")
  {
    std::ostringstream out;
    REQUIRE(write_goto_binary(
      out, goto_model, message_handler, GOTO_BINARY_VERSION - 1));
    // the version is validated before the header is written, so the stream is
    // left untouched
    REQUIRE(out.str().empty());
  }

  SECTION("a version above the supported one is rejected, nothing written")
  {
    std::ostringstream out;
    REQUIRE(write_goto_binary(
      out, goto_model, message_handler, GOTO_BINARY_VERSION + 1));
    REQUIRE(out.str().empty());
  }

  SECTION("the supported version is written successfully")
  {
    std::ostringstream out;
    REQUIRE_FALSE(write_goto_binary(out, goto_model, message_handler));
    REQUIRE_FALSE(out.str().empty());
  }
}
