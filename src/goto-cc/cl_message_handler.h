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

  /// With \p yes set to \c true, prefix warnings with an error message.
  /// \param yes: Whether or not to prefix warnings.
  void print_warnings_as_errors(bool yes)
  {
    warnings_are_errors = yes;
  }

private:
  bool warnings_are_errors = false;
};

#endif // CPROVER_GOTO_CC_CL_MESSAGE_HANDLER_H
