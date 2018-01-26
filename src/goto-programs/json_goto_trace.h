/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

Date: November 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#ifndef CPROVER_GOTO_PROGRAMS_JSON_GOTO_TRACE_H
#define CPROVER_GOTO_PROGRAMS_JSON_GOTO_TRACE_H

#include <util/json.h>
#include <util/json_stream.h>

#include "goto_trace.h"

#include "json_goto_trace.h"

#include <util/json_expr.h>
#include <util/arith_tools.h>
#include <util/config.h>
#include <util/invariant.h>
#include <util/simplify_expr.h>

#include <langapi/language_util.h>
#include <util/json_irep.h>

typedef struct
{
  jsont &location;
  const goto_trace_stept& step;
  const namespacet &ns;
  const source_locationt &source_location;
} conversion_dependenciest;

void convert_assert(json_objectt &json_failure,
  conversion_dependenciest &conversion_dependencies);

void convert_decl(json_objectt &json_assignment,
 conversion_dependenciest &conversion_dependencies);

void convert_output(json_objectt &json_output,
 conversion_dependenciest &conversion_dependencies);

void convert_input(json_objectt &json_input,
 conversion_dependenciest &conversion_dependencies);

void convert_return(json_objectt &json_call_return,
  conversion_dependenciest &conversion_dependencies);

void convert_default(json_objectt &json_location_only,
  conversion_dependenciest &conversion_dependencies);

template<typename newJson>
void convert(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  newJson &dest)
{
  source_locationt previous_source_location;

  for(const auto &step : goto_trace.steps)
  {
    const source_locationt &source_location=step.pc->source_location;

    jsont json_location;

    source_location.is_not_nil()&&source_location.get_file()!=""?
        json_location=json(source_location):
        json_location=json_nullt();

    conversion_dependenciest conversion_dependencies=
    {
       json_location, step, ns, source_location
    };

    switch(step.type)
    {
    case goto_trace_stept::typet::ASSERT:
      if(!step.cond_value)
      {
        json_objectt &json_failure=dest.push_back().make_object();
        convert_assert(json_failure, conversion_dependencies);
      }
      break;

    case goto_trace_stept::typet::ASSIGNMENT:
    case goto_trace_stept::typet::DECL:
      {
        json_objectt &json_assignment=dest.push_back().make_object();
        convert_decl(json_assignment, conversion_dependencies);
      }
      break;

    case goto_trace_stept::typet::OUTPUT:
      {
        json_objectt &json_output=dest.push_back().make_object();
        convert_output(json_output, conversion_dependencies);
      }
      break;

    case goto_trace_stept::typet::INPUT:
      {
        json_objectt &json_input=dest.push_back().make_object();
        convert_input(json_input, conversion_dependencies);
      }
      break;

    case goto_trace_stept::typet::FUNCTION_CALL:
    case goto_trace_stept::typet::FUNCTION_RETURN:
      {
        json_objectt &json_call_return=dest.push_back().make_object();
        convert_return(json_call_return, conversion_dependencies);
      }
      break;

    default:
      if(source_location!=previous_source_location)
      {
        // just the source location
        if(!json_location.is_null())
        {
          json_objectt &json_location_only=dest.push_back().make_object();
          convert_default(json_location_only, conversion_dependencies);
        }
      }
    }

    if(source_location.is_not_nil() && source_location.get_file()!="")
      previous_source_location=source_location;
  }
}

#endif
