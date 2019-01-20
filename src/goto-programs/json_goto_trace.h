/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

Date: November 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#ifndef CPROVER_GOTO_PROGRAMS_JSON_GOTO_TRACE_H
#define CPROVER_GOTO_PROGRAMS_JSON_GOTO_TRACE_H

#include "goto_trace.h"

#include <util/invariant.h>
#include <util/json.h>
#include <util/json_irep.h>
#include <util/json_stream.h>

/// This is structure is here to facilitate
/// passing arguments to the conversion
/// functions.
typedef struct
{
  const jsont &location;
  const goto_trace_stept &step;
  const namespacet &ns;
} conversion_dependenciest;

/// Convert an ASSERT goto_trace step.
/// \param [out] json_failure: The JSON object that
///   will contain the information about the step
///   after this function has run.
/// \param conversion_dependencies: A structure
///   that contains information the conversion function
///   needs.
void convert_assert(
  json_objectt &json_failure,
  const conversion_dependenciest &conversion_dependencies);

/// Convert a DECL goto_trace step.
/// \param [out] json_assignment: The JSON object that
///   will contain the information about the step
///   after this function has run.
/// \param conversion_dependencies: A structure
///   that contains information the conversion function
///   needs.
/// \param trace_options: Extra information used by this
///   particular conversion function.
void convert_decl(
  json_objectt &json_assignment,
  const conversion_dependenciest &conversion_dependencies,
  const trace_optionst &trace_options);

/// Convert an OUTPUT goto_trace step.
/// \param [out] json_output: The JSON object that
///   will contain the information about the step
///   after this function has run.
/// \param conversion_dependencies: A structure
///   that contains information the conversion function
///   needs.
void convert_output(
  json_objectt &json_output,
  const conversion_dependenciest &conversion_dependencies);

/// Convert an INPUT goto_trace step.
/// \param [out] json_input: The JSON object that
///   will contain the information about the step
///   after this function has run.
/// \param conversion_dependencies: A structure
///   that contains information the conversion function
///   needs.
void convert_input(
  json_objectt &json_input,
  const conversion_dependenciest &conversion_dependencies);

/// Convert a FUNCTION_RETURN goto_trace step.
/// \param [out] json_call_return: The JSON object that
///   will contain the information about the step
///   after this function has run.
/// \param conversion_dependencies: A structure
///   that contains information the conversion function
///   needs.
void convert_return(
  json_objectt &json_call_return,
  const conversion_dependenciest &conversion_dependencies);

/// Convert all other types of steps not already handled
/// by the other conversion functions.
/// \param [out] json_location_only: The JSON object that
///   will contain the information about the step
///   after this function has run.
/// \param conversion_dependencies: A structure
///   that contains information the conversion function
///   needs.
void convert_default(
  json_objectt &json_location_only,
  const conversion_dependenciest &conversion_dependencies);

/// Templated version of the conversion method.
/// Works by dispatching to the more specialised
/// conversion functions based on the type of the
/// step that is being handled.
/// \param ns: The namespace used for resolution of symbols.
/// \param goto_trace: The goto_trace from which we are
///   going to convert the steps from.
/// \param dest_array: The JSON object that we are going
///   to append the step information to.
/// \param trace_options: A list of trace options
template <typename json_arrayT>
void convert(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  json_arrayT &dest_array,
  trace_optionst trace_options = trace_optionst::default_options)
{
  source_locationt previous_source_location;

  for(const auto &step : goto_trace.steps)
  {
    const source_locationt &source_location = step.pc->source_location;

    jsont json_location;

    source_location.is_not_nil() && !source_location.get_file().empty()
      ? json_location = json(source_location)
      : json_location = json_nullt();

    // NOLINTNEXTLINE(whitespace/braces)
    conversion_dependenciest conversion_dependencies = {
      json_location, step, ns};

    switch(step.type)
    {
    case goto_trace_stept::typet::ASSERT:
      if(!step.cond_value)
      {
        json_objectt &json_failure = dest_array.push_back().make_object();
        convert_assert(json_failure, conversion_dependencies);
      }
      break;

    case goto_trace_stept::typet::ASSIGNMENT:
    case goto_trace_stept::typet::DECL:
    {
      json_objectt &json_assignment = dest_array.push_back().make_object();
      convert_decl(json_assignment, conversion_dependencies, trace_options);
    }
    break;

    case goto_trace_stept::typet::OUTPUT:
    {
      json_objectt &json_output = dest_array.push_back().make_object();
      convert_output(json_output, conversion_dependencies);
    }
    break;

    case goto_trace_stept::typet::INPUT:
    {
      json_objectt &json_input = dest_array.push_back().make_object();
      convert_input(json_input, conversion_dependencies);
    }
    break;

    case goto_trace_stept::typet::FUNCTION_CALL:
    case goto_trace_stept::typet::FUNCTION_RETURN:
    {
      json_objectt &json_call_return = dest_array.push_back().make_object();
      convert_return(json_call_return, conversion_dependencies);
    }
    break;

    default:
      if(source_location != previous_source_location)
      {
        json_objectt &json_location_only = dest_array.push_back().make_object();
        convert_default(json_location_only, conversion_dependencies);
      }
    }

    if(source_location.is_not_nil() && !source_location.get_file().empty())
      previous_source_location = source_location;
  }
}

#endif // CPROVER_GOTO_PROGRAMS_JSON_GOTO_TRACE_H
