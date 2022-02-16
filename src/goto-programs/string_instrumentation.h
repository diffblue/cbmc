/*******************************************************************\

Module: String Abstraction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// String Abstraction

#ifndef CPROVER_GOTO_PROGRAMS_STRING_INSTRUMENTATION_H
#define CPROVER_GOTO_PROGRAMS_STRING_INSTRUMENTATION_H

#include <util/exception_utils.h>

class exprt;
class goto_functionst;
class goto_modelt;
class goto_programt;
class symbol_tablet;

class incorrect_source_program_exceptiont : public cprover_exception_baset
{
public:
  incorrect_source_program_exceptiont(
    std::string message,
    source_locationt source_location)
    : cprover_exception_baset(std::move(message)),
      source_location(std::move(source_location))
  {
  }
  std::string what() const override
  {
    return reason + " (at: " + source_location.as_string() + ")";
  }

private:
  source_locationt source_location;
};

void string_instrumentation(
  symbol_tablet &,
  goto_programt &);

void string_instrumentation(
  symbol_tablet &,
  goto_functionst &);

void string_instrumentation(goto_modelt &);

exprt is_zero_string(const exprt &what, bool write = false);
exprt zero_string_length(const exprt &what, bool write=false);
exprt buffer_size(const exprt &what);

#endif // CPROVER_GOTO_PROGRAMS_STRING_INSTRUMENTATION_H
