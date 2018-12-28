/*******************************************************************\

Module: Print messages like CL.exe does

Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_GOTO_CC_CL_MESSAGE_HANDLER_H
#define CPROVER_GOTO_CC_CL_MESSAGE_HANDLER_H

#include <util/cout_message.h>

class cl_message_handlert : public console_message_handlert
{
public:
  void print(unsigned, const xmlt &) override
  {
  }

  void print(unsigned, const jsont &) override
  {
  }

  // aims to imitate the messages CL prints
  void print(
    unsigned level,
    const std::string &message,
    const source_locationt &location) override;

  using console_message_handlert::print;
};

#endif // CPROVER_GOTO_CC_CL_MESSAGE_HANDLER_H
