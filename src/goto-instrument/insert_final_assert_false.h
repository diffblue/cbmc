/*******************************************************************\

Module: Insert assert(false) at end of entry function

Author: Nathan Chong, Kareem Khazem

\*******************************************************************/

/// \file
/// Insert final assert false into a function

/// This transform can be used to check for some cases of vacuous proofs
/// Usually the given function is the test harness / entry point
/// The instrumented assert is expected to fail
/// If it does not then this may indicate inconsistent assumptions

#ifndef CPROVER_GOTO_INSTRUMENT_INSERT_FINAL_ASSERT_FALSE_H
#define CPROVER_GOTO_INSTRUMENT_INSERT_FINAL_ASSERT_FALSE_H

#include <string>

#include <util/message.h>

class goto_modelt;

class insert_final_assert_falset
{
public:
  explicit insert_final_assert_falset(message_handlert &_message_handler);
  bool operator()(goto_modelt &, const std::string &);

private:
  messaget log;
};

/// Transform a goto program by inserting assert(false) at the end of a given
/// function \p function_to_instrument. The instrumented assert is expected
/// to fail. If it does not then this may indicate inconsistent assumptions.
///
/// \param goto_model: The goto program to modify.
/// \param function_to_instrument: Name of the function to instrument.
/// \param message_handler: Handles logging.
/// \returns false on success
bool insert_final_assert_false(
  goto_modelt &goto_model,
  const std::string &function_to_instrument,
  message_handlert &message_handler);

// clang-format off
#define OPT_INSERT_FINAL_ASSERT_FALSE \
  "(insert-final-assert-false):"

#define HELP_INSERT_FINAL_ASSERT_FALSE \
  " --insert-final-assert-false <function>\n" \
  /* NOLINTNEXTLINE(whitespace/line_length) */ \
  "                              generate assert(false) at end of function\n"
// clang-format on

#endif // CPROVER_GOTO_INSTRUMENT_INSERT_FINAL_ASSERT_FALSE_H
