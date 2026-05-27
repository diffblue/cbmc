/*******************************************************************\

Module: ui_message_handlert tests

Author: Michael Tautschnig

\*******************************************************************/

#include <util/cmdline.h>
#include <util/message.h>
#include <util/ui_message.h>

#include <testing-utils/use_catch.h>

#include <iostream>
#include <memory>
#include <sstream>

/// Construct a ui_message_handlert via the cmdlinet ctor (the usual
/// path for every CBMC tool). For XML_UI / JSON_UI the cmdlinet ctor
/// leaves the underlying message_handler null; this is the
/// configuration that exercises the regression fixed in this PR. The
/// XML/JSON ctors write a header to std::cout, so we redirect cout to
/// a throw-away stream around the call.
static std::unique_ptr<ui_message_handlert>
make_handler(ui_message_handlert::uit ui)
{
  cmdlinet cmdline;
  // Register the options before we can set them; the cmdlinet ctor
  // for ui_message_handlert dispatches on isset("xml-ui") /
  // isset("json-ui").
  const char *argv0[] = {"unit-test"};
  cmdline.parse(1, argv0, "(xml-ui)(json-ui)");
  switch(ui)
  {
  case ui_message_handlert::uit::PLAIN:
    break;
  case ui_message_handlert::uit::XML_UI:
    cmdline.set("xml-ui");
    break;
  case ui_message_handlert::uit::JSON_UI:
    cmdline.set("json-ui");
    break;
  }

  std::ostringstream sink;
  std::streambuf *const saved = std::cout.rdbuf(sink.rdbuf());
  auto handler = std::make_unique<ui_message_handlert>(cmdline, "test");
  std::cout.rdbuf(saved);
  return handler;
}

/// quote_begin and quote_end are encoded as the ASCII codes for '<'
/// (60) and '>' (62) respectively. ui_message_handlert::command must
/// render both as a single quote on every UI; in particular the XML
/// and JSON variants -- where the underlying message_handler is null
/// when constructed via the cmdlinet ctor -- must also do so
/// (regression: prior to PR #5696's reorder the structured UIs
/// silently dropped these characters).
TEST_CASE(
  "ui_message_handlert renders quote_begin/quote_end as ' (PLAIN)",
  "[core][util][ui_message]")
{
  auto handler = make_handler(ui_message_handlert::uit::PLAIN);
  // command() is protected on ui_message_handlert; call through the
  // message_handlert public interface.
  const message_handlert &mh = *handler;
  CHECK(mh.command('<') == "'");
  CHECK(mh.command('>') == "'");
}

TEST_CASE(
  "ui_message_handlert renders quote_begin/quote_end as ' (XML)",
  "[core][util][ui_message]")
{
  auto handler = make_handler(ui_message_handlert::uit::XML_UI);
  const message_handlert &mh = *handler;
  CHECK(mh.command('<') == "'");
  CHECK(mh.command('>') == "'");
}

TEST_CASE(
  "ui_message_handlert renders quote_begin/quote_end as ' (JSON)",
  "[core][util][ui_message]")
{
  auto handler = make_handler(ui_message_handlert::uit::JSON_UI);
  const message_handlert &mh = *handler;
  CHECK(mh.command('<') == "'");
  CHECK(mh.command('>') == "'");
}

/// is_sgr_style_command must return true for every messaget styling
/// command and false for the quote commands and arbitrary other codes.
/// The point of the helper is to be the single source of truth for
/// "which commands are SGR-style"; this test pins the helper's output
/// against the messaget::commandt constants so that adding or
/// removing a styling command in messaget without updating the helper
/// (or vice versa) is caught at unit-test time.
TEST_CASE(
  "ui_message_handlert::is_sgr_style_command matches messaget styling codes",
  "[core][util][ui_message]")
{
  // Every styling command on messaget should be classified as SGR.
  for(const auto &cmd :
      {messaget::reset,
       messaget::bold,
       messaget::faint,
       messaget::italic,
       messaget::underline,
       messaget::red,
       messaget::green,
       messaget::yellow,
       messaget::blue,
       messaget::magenta,
       messaget::cyan,
       messaget::bright_red,
       messaget::bright_green,
       messaget::bright_yellow,
       messaget::bright_blue,
       messaget::bright_magenta,
       messaget::bright_cyan})
  {
    CHECK(ui_message_handlert::is_sgr_style_command(cmd.command));
  }

  // quote_begin / quote_end are commands but NOT SGR-style.
  CHECK_FALSE(
    ui_message_handlert::is_sgr_style_command(messaget::quote_begin.command));
  CHECK_FALSE(
    ui_message_handlert::is_sgr_style_command(messaget::quote_end.command));

  // Arbitrary non-styling codes outside the SGR ranges should be rejected.
  CHECK_FALSE(ui_message_handlert::is_sgr_style_command(5));
  CHECK_FALSE(ui_message_handlert::is_sgr_style_command(30));
  CHECK_FALSE(ui_message_handlert::is_sgr_style_command(37));
  CHECK_FALSE(ui_message_handlert::is_sgr_style_command(90));
  CHECK_FALSE(ui_message_handlert::is_sgr_style_command(97));
  CHECK_FALSE(ui_message_handlert::is_sgr_style_command(256));
}
