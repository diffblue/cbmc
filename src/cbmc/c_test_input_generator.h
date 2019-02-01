/*******************************************************************\

Module: Test Input Generator for C

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Test Input Generator for C

#ifndef CPROVER_CBMC_C_TEST_INPUT_GENERATOR_H
#define CPROVER_CBMC_C_TEST_INPUT_GENERATOR_H

#include <iosfwd>

#include <util/ui_message.h>

class goto_tracet;
class goto_trace_storaget;
class json_objectt;
class namespacet;
class optionst;

class test_inputst
{
public:
  /// Outputs the test inputs in plain text format
  void output_plain_text(
    std::ostream &out,
    const namespacet &ns,
    const goto_tracet &goto_trace) const;

  /// Returns the test inputs in JSON format
  /// including the trace if desired
  json_objectt to_json(
    const namespacet &ns,
    const goto_tracet &goto_trace,
    bool print_trace) const;

  /// Returns the test inputs in XML format
  /// including the trace if desired
  xmlt to_xml(
    const namespacet &ns,
    const goto_tracet &goto_trace,
    bool print_trace) const;
};

class c_test_input_generatort
{
public:
  c_test_input_generatort(
    ui_message_handlert &ui_message_handler,
    const optionst &options);

  /// Extracts test inputs for all traces and outputs them
  void operator()(const goto_trace_storaget &);

protected:
  ui_message_handlert &ui_message_handler;
  const optionst &options;

  /// Extracts test inputs from the given \p goto_trace
  test_inputst operator()(const goto_tracet &goto_trace, const namespacet &ns);
};

#endif // CPROVER_CBMC_C_TEST_INPUT_GENERATOR_H
