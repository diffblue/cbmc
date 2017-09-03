/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: November 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#include "json_goto_trace.h"

#include <cassert>

#include <util/json_expr.h>

#include <langapi/language_util.h>

void convert(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  jsont &dest)
{
  json_arrayt &dest_array=dest.make_array();

  source_locationt previous_source_location;

  for(const auto &step : goto_trace.steps)
  {
    const source_locationt &source_location=step.pc->source_location;

    jsont json_location;

    if(source_location.is_not_nil() && source_location.get_file()!="")
      json_location=json(source_location);
    else
      json_location=json_nullt();

    switch(step.type)
    {
    case goto_trace_stept::typet::ASSERT:
      if(!step.cond_value)
      {
        irep_idt property_id;

        if(step.pc->is_assert())
          property_id=source_location.get_property_id();
        else if(step.pc->is_goto()) // unwinding, we suspect
        {
          property_id=
            id2string(step.pc->source_location.get_function())+
            ".unwind."+std::to_string(step.pc->loop_number);
        }

        json_objectt &json_failure=dest_array.push_back().make_object();

        json_failure["stepType"]=json_stringt("failure");
        json_failure["hidden"]=jsont::json_boolean(step.hidden);
        json_failure["internal"]=jsont::json_boolean(step.internal);
        json_failure["thread"]=json_numbert(std::to_string(step.thread_nr));
        json_failure["reason"]=json_stringt(id2string(step.comment));
        json_failure["property"]=json_stringt(id2string(property_id));

        if(!json_location.is_null())
          json_failure["sourceLocation"]=json_location;
      }
      break;

    case goto_trace_stept::typet::ASSIGNMENT:
    case goto_trace_stept::typet::DECL:
      {
        irep_idt identifier=step.lhs_object.get_identifier();
        json_objectt &json_assignment=dest_array.push_back().make_object();

        json_assignment["stepType"]=json_stringt("assignment");

        if(!json_location.is_null())
          json_assignment["sourceLocation"]=json_location;

        std::string value_string, binary_string, type_string, full_lhs_string;
        json_objectt full_lhs_value;

        if(step.full_lhs.is_not_nil())
          full_lhs_string=from_expr(ns, identifier, step.full_lhs);

#if 0
        if(it.full_lhs_value.is_not_nil())
          full_lhs_value_string=from_expr(ns, identifier, it.full_lhs_value);
#endif

        if(step.full_lhs_value.is_not_nil())
          full_lhs_value = json(step.full_lhs_value, ns);

        const symbolt *symbol;
        irep_idt base_name, display_name;

        if(!ns.lookup(identifier, symbol))
        {
          base_name=symbol->base_name;
          display_name=symbol->display_name();
          if(type_string=="")
            type_string=from_type(ns, identifier, symbol->type);

          json_assignment["mode"]=json_stringt(id2string(symbol->mode));
        }

        json_assignment["value"]=full_lhs_value;
        json_assignment["lhs"]=json_stringt(full_lhs_string);
        json_assignment["hidden"]=jsont::json_boolean(step.hidden);
        json_assignment["internal"]=jsont::json_boolean(step.internal);
        json_assignment["thread"]=json_numbert(std::to_string(step.thread_nr));

        json_assignment["assignmentType"]=
          json_stringt(
            step.assignment_type==
              goto_trace_stept::assignment_typet::ACTUAL_PARAMETER?
            "actual-parameter":
            "variable");
      }
      break;

    case goto_trace_stept::typet::OUTPUT:
      {
        json_objectt &json_output=dest_array.push_back().make_object();

        json_output["stepType"]=json_stringt("output");
        json_output["hidden"]=jsont::json_boolean(step.hidden);
        json_output["internal"]=jsont::json_boolean(step.internal);
        json_output["thread"]=json_numbert(std::to_string(step.thread_nr));
        json_output["outputID"]=json_stringt(id2string(step.io_id));

        json_arrayt &json_values=json_output["values"].make_array();

        for(const auto &arg : step.io_args)
        {
          if(arg.is_nil())
            json_values.push_back(json_stringt(""));
          else
            json_values.push_back(json(arg, ns));
        }

        if(!json_location.is_null())
          json_output["sourceLocation"]=json_location;
      }
      break;

    case goto_trace_stept::typet::INPUT:
      {
        json_objectt &json_input=dest_array.push_back().make_object();

        json_input["stepType"]=json_stringt("input");
        json_input["hidden"]=jsont::json_boolean(step.hidden);
        json_input["internal"]=jsont::json_boolean(step.internal);
        json_input["thread"]=json_numbert(std::to_string(step.thread_nr));
        json_input["inputID"]=json_stringt(id2string(step.io_id));

        json_arrayt &json_values=json_input["values"].make_array();

        for(const auto &arg : step.io_args)
        {
          if(arg.is_nil())
            json_values.push_back(json_stringt(""));
          else
            json_values.push_back(json(arg, ns));
        }

        if(!json_location.is_null())
          json_input["sourceLocation"]=json_location;
      }
      break;

    case goto_trace_stept::typet::FUNCTION_CALL:
    case goto_trace_stept::typet::FUNCTION_RETURN:
      {
        std::string tag=
          (step.type==goto_trace_stept::typet::FUNCTION_CALL)?
            "function-call":"function-return";
        json_objectt &json_call_return=dest_array.push_back().make_object();

        json_call_return["stepType"]=json_stringt(tag);
        json_call_return["hidden"]=jsont::json_boolean(step.hidden);
        json_call_return["internal"]=jsont::json_boolean(step.internal);
        json_call_return["thread"]=json_numbert(std::to_string(step.thread_nr));

        const symbolt &symbol=ns.lookup(step.identifier);
        json_objectt &json_function=json_call_return["function"].make_object();
        json_function["displayName"]=
          json_stringt(id2string(symbol.display_name()));
        json_function["identifier"]=json_stringt(id2string(step.identifier));
        json_function["sourceLocation"]=json(symbol.location);

        if(!json_location.is_null())
          json_call_return["sourceLocation"]=json_location;
      }
      break;

    default:
      if(source_location!=previous_source_location)
      {
        // just the source location
        if(!json_location.is_null())
        {
          json_objectt &json_location_only=dest_array.push_back().make_object();
          json_location_only["stepType"]=json_stringt("location-only");
          json_location_only["hidden"]=jsont::json_boolean(step.hidden);
          json_location_only["internal"]=jsont::json_boolean(step.internal);
          json_location_only["thread"]=
            json_numbert(std::to_string(step.thread_nr));
          json_location_only["sourceLocation"]=json_location;
        }
      }
    }

    if(source_location.is_not_nil() && source_location.get_file()!="")
      previous_source_location=source_location;
  }
}
