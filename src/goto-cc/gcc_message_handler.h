/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_CC_GCC_MESSAGE_HANDLER_H
#define CPROVER_GOTO_CC_GCC_MESSAGE_HANDLER_H

#include <util/cout_message.h>

class gcc_message_handlert : public console_message_handlert
{
public:
  void print(unsigned, const xmlt &) override
  {
  }

  void print(unsigned, const jsont &) override
  {
  }

  // aims to imitate the messages gcc prints
  void print(unsigned level, const std::string &message) override;

  void print(
    unsigned level,
    const std::string &message,
    const source_locationt &location) override;

  /// With \p yes set to \c true, prefix warnings with "error:" instead of
  /// "warning:".
  /// \param yes: Whether or not to prefix warnings with "error:".
  void print_warnings_as_errors(bool yes)
  {
    warnings_are_errors = yes;
  }

private:
  bool warnings_are_errors = false;

  /// feed a command into a string
  std::string string(const messaget::commandt &c) const
  {
    return command(c.command);
  }
};

#endif // CPROVER_GOTO_CC_GCC_MESSAGE_HANDLER_H
