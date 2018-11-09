/*******************************************************************\

Module: Messaget tests

Author: Diffblue Ltd.

\*******************************************************************/

#include <sstream>
#include <string.h>
#include <testing-utils/use_catch.h>
#include <util/message.h>

TEST_CASE("Copy a messaget")
{
  std::ostringstream sstream1, sstream2;
  stream_message_handlert handler1(sstream1), handler2(sstream2);

  messaget msg1(handler1);

  // Copy messaget:
  messaget msg2(msg1);

  // Change its handler:
  msg2.set_message_handler(handler2);

  msg2.status() << "Test" << messaget::eom;

  CHECK(sstream1.str()=="");
  CHECK(sstream2.str()=="Test\n");
}

TEST_CASE("Assign a messaget")
{
  std::ostringstream sstream1, sstream2;
  stream_message_handlert handler1(sstream1), handler2(sstream2);

  messaget msg1(handler1);

  // Assign messaget:
  messaget msg2;
  msg2=msg1;

  // Change its handler:
  msg2.set_message_handler(handler2);

  msg2.status() << "Test" << messaget::eom;

  CHECK(sstream1.str()=="");
  CHECK(sstream2.str()=="Test\n");
}
