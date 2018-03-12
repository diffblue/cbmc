/*******************************************************************\

 Module: Unit test utilities

 Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Utility for converting strings in to exprt, throwing a CATCH exception
/// if this fails in any way.

#ifndef CPROVER_TESTING_UTILS_C_TO_EXPR_H
#define CPROVER_TESTING_UTILS_C_TO_EXPR_H

#include <memory>

#include <util/expr.h>
#include <util/message.h>
#include <util/ui_message.h>
#include <util/namespace.h>
#include <ansi-c/ansi_c_language.h>

class c_to_exprt
{
public:
  c_to_exprt();
  exprt operator()(const std::string &input_string, const namespacet &ns);

private:
  std::unique_ptr<message_handlert> message_handler;
  ansi_c_languaget language;
};

#endif // CPROVER_TESTING_UTILS_C_TO_EXPR_H
