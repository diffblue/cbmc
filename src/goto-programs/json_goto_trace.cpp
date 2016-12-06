/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: November 2005

\*******************************************************************/

#include <cassert>

#include <util/i2string.h>
#include <util/json_expr.h>

#include <langapi/language_util.h>

#include "json_goto_trace.h"

/*******************************************************************\

Function: convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  jsont &dest)
{
  json_arrayt &dest_array=dest.make_array();

  source_locationt previous_source_location;

  for(const auto & it : goto_trace.steps)
  {
    const source_locationt &source_location=it.pc->source_location;

    jsont json_location;

    if(source_location.is_not_nil() && source_location.get_file()!="")
      json_location=json(source_location);
    else
      json_location=json_nullt();

    switch(it.type)
    {
    case goto_trace_stept::ASSERT:
      if(!it.cond_value)
      {
        irep_idt property_id;

        if(it.pc->is_assert())
          property_id=source_location.get_property_id();
        else if(it.pc->is_goto()) // unwinding, we suspect
        {
          property_id=
            id2string(it.pc->source_location.get_function())+".unwind."+
            i2string(it.pc->loop_number);
        }

        json_objectt &json_failure=dest_array.push_back().make_object();

        json_failure["stepType"]=json_stringt("failure");
        json_failure["hidden"]=jsont::json_boolean(it.hidden);
        json_failure["thread"]=json_numbert(i2string(it.thread_nr));
        json_failure["reason"]=json_stringt(id2string(it.comment));
        json_failure["property"]=json_stringt(id2string(property_id));

        if(!json_location.is_null())
          json_failure["sourceLocation"]=json_location;
      }
      break;

    case goto_trace_stept::ASSIGNMENT:
    case goto_trace_stept::DECL:
      {
        irep_idt identifier=it.lhs_object.get_identifier();
        json_objectt &json_assignment=dest_array.push_back().make_object();

        json_assignment["stepType"]=json_stringt("assignment");

        if(!json_location.is_null())
          json_assignment["sourceLocation"]=json_location;

        std::string value_string, binary_string, type_string, full_lhs_string;
        json_objectt full_lhs_value;

        if(it.full_lhs.is_not_nil())
          full_lhs_string=from_expr(ns, identifier, it.full_lhs);

#if 0
        if(it.full_lhs_value.is_not_nil())
          full_lhs_value_string=from_expr(ns, identifier, it.full_lhs_value);
#endif

        if(it.full_lhs_value.is_not_nil())
          full_lhs_value = json(it.full_lhs_value, ns);

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
        json_assignment["hidden"]=jsont::json_boolean(it.hidden);
        json_assignment["thread"]=json_numbert(i2string(it.thread_nr));

        json_assignment["assignmentType"]=
          json_stringt(it.assignment_type==goto_trace_stept::ACTUAL_PARAMETER?
                       "actual-parameter":"variable");
      }
      break;

    case goto_trace_stept::OUTPUT:
      {
        json_objectt &json_output=dest_array.push_back().make_object();

        json_output["stepType"]=json_stringt("output");
        json_output["hidden"]=jsont::json_boolean(it.hidden);
        json_output["thread"]=json_numbert(i2string(it.thread_nr));
        json_output["outputID"]=json_stringt(id2string(it.io_id));

        json_arrayt &json_values=json_output["values"].make_array();

        for(const auto l_it : it.io_args)
        {
          if(l_it.is_nil())
            json_values.push_back(json_stringt(""));
          else
            json_values.push_back(json(l_it, ns));
        }

        if(!json_location.is_null())
          json_output["sourceLocation"]=json_location;
      }
      break;

    case goto_trace_stept::INPUT:
      {
        json_objectt &json_input=dest_array.push_back().make_object();

        json_input["stepType"]=json_stringt("input");
        json_input["hidden"]=jsont::json_boolean(it.hidden);
        json_input["thread"]=json_numbert(i2string(it.thread_nr));
        json_input["inputID"]=json_stringt(id2string(it.io_id));

        json_arrayt &json_values=json_input["values"].make_array();

        for(const auto l_it : it.io_args)
        {
          if(l_it.is_nil())
            json_values.push_back(json_stringt(""));
          else
            json_values.push_back(json(l_it, ns));
        }

        if(!json_location.is_null())
          json_input["sourceLocation"]=json_location;
      }
      break;

    case goto_trace_stept::FUNCTION_CALL:
    case goto_trace_stept::FUNCTION_RETURN:
      {
        std::string tag=
          (it.type==goto_trace_stept::FUNCTION_CALL)?
            "function-call":"function-return";
        json_objectt &json_call_return=dest_array.push_back().make_object();

        json_call_return["stepType"]=json_stringt(tag);
        json_call_return["hidden"]=jsont::json_boolean(it.hidden);
        json_call_return["thread"]=json_numbert(i2string(it.thread_nr));

        const symbolt &symbol=ns.lookup(it.identifier);
        json_objectt &json_function=json_call_return["function"].make_object();
        json_function["displayName"]=
          json_stringt(id2string(symbol.display_name()));
        json_function["identifier"]=json_stringt(id2string(it.identifier));
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
          json_location_only["hidden"]=jsont::json_boolean(it.hidden);
          json_location_only["thread"]=json_numbert(i2string(it.thread_nr));
          json_location_only["sourceLocation"]=json_location;
        }
      }
    }

    if(source_location.is_not_nil() && source_location.get_file()!="")
      previous_source_location=source_location;
  }
}
