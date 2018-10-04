/*******************************************************************\

Module: String Abstraction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// String Abstraction

#ifndef CPROVER_GOTO_PROGRAMS_STRING_INSTRUMENTATION_H
#define CPROVER_GOTO_PROGRAMS_STRING_INSTRUMENTATION_H

#include "goto_functions.h"

#include <util/exception_utils.h>

class message_handlert;
class goto_modelt;

class incorrect_source_program_exceptiont : public cprover_exception_baset
{
public:
  incorrect_source_program_exceptiont(
    std::string message,
    source_locationt source_location)
    : message(std::move(message)), source_location(std::move(source_location))
  {
  }
  std::string what() const override
  {
    return message + " (at: " + source_location.as_string() + ")";
  }

private:
  std::string message;
  source_locationt source_location;
};

void string_instrumentation(
  symbol_tablet &,
  message_handlert &,
  goto_programt &);

void string_instrumentation(
  symbol_tablet &,
  message_handlert &,
  goto_functionst &);

void string_instrumentation(
  goto_modelt &,
  message_handlert &);

exprt is_zero_string(const exprt &what, bool write=false);
exprt zero_string_length(const exprt &what, bool write=false);
exprt buffer_size(const exprt &what);

#endif // CPROVER_GOTO_PROGRAMS_STRING_INSTRUMENTATION_H
