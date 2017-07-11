/*******************************************************************\

 Module: Unit test utilities

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Utility for converting strings in to exprt, throwing a CATCH exception
/// if this fails in any way.
///
#include "c_to_expr.h"

#include <catch.hpp>

c_to_exprt::c_to_exprt():
  message_handler(
    std::unique_ptr<message_handlert>(new ui_message_handlert()))
{
  language.set_message_handler(*message_handler);
}

/// Take an input string that should be a valid C rhs expression
/// \param input_string: The string to convert
/// \param ns: The global namespace
/// \return: A constructed expr representing the string
exprt c_to_exprt::operator()(
  const std::string &input_string, const namespacet &ns)
{
  exprt expr;
  bool result=language.to_expr(input_string, "",  expr, ns);
  REQUIRE(!result);
  return expr;
}
