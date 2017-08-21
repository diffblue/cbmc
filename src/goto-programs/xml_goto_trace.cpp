/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: November 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#include "xml_goto_trace.h"

#include <cassert>

#include <util/xml_expr.h>
#include <util/symbol.h>

#include <ansi-c/printf_formatter.h>
#include <langapi/language_util.h>

void convert(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  xmlt &dest)
{
  dest=xmlt("goto_trace");

  source_locationt previous_source_location;

  for(const auto &step : goto_trace.steps)
  {
    const source_locationt &source_location=step.get_pc()->source_location;

    xmlt xml_location;
    if(source_location.is_not_nil() && source_location.get_file()!="")
      xml_location=xml(source_location);

    switch(step.type)
    {
    case goto_trace_stept::typet::ASSERT:
      if(!step.cond_value)
      {
        irep_idt property_id;

        if(step.get_pc()->is_assert())
          property_id=source_location.get_property_id();
        else if(step.get_pc()->is_goto()) // unwinding, we suspect
        {
          property_id=
            id2string(step.get_pc()->source_location.get_function())+
            ".unwind."+std::to_string(step.get_pc()->loop_number);
        }

        xmlt &xml_failure=dest.new_element("failure");

        xml_failure.set_attribute_bool("hidden", step.hidden);
        xml_failure.set_attribute("thread", std::to_string(step.thread_nr));
        xml_failure.set_attribute("step_nr", std::to_string(step.step_nr));
        xml_failure.set_attribute("reason", id2string(step.comment));
        xml_failure.set_attribute("property", id2string(property_id));

        if(xml_location.name!="")
          xml_failure.new_element().swap(xml_location);
      }
      break;

    case goto_trace_stept::typet::ASSIGNMENT:
    case goto_trace_stept::typet::DECL:
      {
        irep_idt identifier=step.lhs_object.get_identifier();
        xmlt &xml_assignment=dest.new_element("assignment");

        if(xml_location.name!="")
          xml_assignment.new_element().swap(xml_location);

        std::string value_string, binary_string, type_string,
                    full_lhs_string, full_lhs_value_string;

        if(step.lhs_object_value.is_not_nil())
          value_string=from_expr(ns, identifier, step.lhs_object_value);

        if(step.full_lhs.is_not_nil())
          full_lhs_string=from_expr(ns, identifier, step.full_lhs);

        if(step.full_lhs_value.is_not_nil())
          full_lhs_value_string=
            from_expr(ns, identifier, step.full_lhs_value);

        if(step.lhs_object_value.type().is_not_nil())
          type_string=
            from_type(ns, identifier, step.lhs_object_value.type());

        const symbolt *symbol;
        irep_idt base_name, display_name;

        if(!ns.lookup(identifier, symbol))
        {
          base_name=symbol->base_name;
          display_name=symbol->display_name();
          if(type_string=="")
            type_string=from_type(ns, identifier, symbol->type);

          xml_assignment.set_attribute("mode", id2string(symbol->mode));
        }

        xml_assignment.new_element("type").data=type_string;
        xml_assignment.new_element("full_lhs").data=full_lhs_string;
        xml_assignment.new_element("full_lhs_value").data=full_lhs_value_string;
        xml_assignment.new_element("value").data=value_string;

        xml_assignment.set_attribute_bool("hidden", step.hidden);
        xml_assignment.set_attribute("thread", std::to_string(step.thread_nr));
        xml_assignment.set_attribute("identifier", id2string(identifier));
        xml_assignment.set_attribute("base_name", id2string(base_name));
        xml_assignment.set_attribute("display_name", id2string(display_name));
        xml_assignment.set_attribute("step_nr", std::to_string(step.step_nr));

        xml_assignment.set_attribute("assignment_type",
          step.assignment_type==
            goto_trace_stept::assignment_typet::ACTUAL_PARAMETER?
          "actual_parameter":"state");

        if(step.lhs_object_value.is_not_nil())
          xml_assignment.new_element("value_expression").
            new_element(xml(step.lhs_object_value, ns));
      }
      break;

    case goto_trace_stept::typet::OUTPUT:
      {
        printf_formattert printf_formatter(ns);
        printf_formatter(id2string(step.format_string), step.io_args);
        std::string text=printf_formatter.as_string();
        xmlt &xml_output=dest.new_element("output");

        xml_output.new_element("text").data=text;

        xml_output.set_attribute_bool("hidden", step.hidden);
        xml_output.set_attribute("thread", std::to_string(step.thread_nr));
        xml_output.set_attribute("step_nr", std::to_string(step.step_nr));

        if(xml_location.name!="")
          xml_output.new_element().swap(xml_location);

        for(const auto &arg : step.io_args)
        {
          xml_output.new_element("value").data=from_expr(ns, "", arg);
          xml_output.new_element("value_expression").
            new_element(xml(arg, ns));
        }
      }
      break;

    case goto_trace_stept::typet::INPUT:
      {
        xmlt &xml_input=dest.new_element("input");
        xml_input.new_element("input_id").data=id2string(step.io_id);

        xml_input.set_attribute_bool("hidden", step.hidden);
        xml_input.set_attribute("thread", std::to_string(step.thread_nr));
        xml_input.set_attribute("step_nr", std::to_string(step.step_nr));

        for(const auto &arg : step.io_args)
        {
          xml_input.new_element("value").data=from_expr(ns, "", arg);
          xml_input.new_element("value_expression").
            new_element(xml(arg, ns));
        }

        if(xml_location.name!="")
          xml_input.new_element().swap(xml_location);
      }
      break;

    case goto_trace_stept::typet::FUNCTION_CALL:
    case goto_trace_stept::typet::FUNCTION_RETURN:
      {
        std::string tag=
          (step.type==goto_trace_stept::typet::FUNCTION_CALL)?
          "function_call":"function_return";
        xmlt &xml_call_return=dest.new_element(tag);

        xml_call_return.set_attribute_bool("hidden", step.hidden);
        xml_call_return.set_attribute("thread", std::to_string(step.thread_nr));
        xml_call_return.set_attribute("step_nr", std::to_string(step.step_nr));

        const symbolt &symbol=ns.lookup(step.identifier);
        xmlt &xml_function=xml_call_return.new_element("function");
        xml_function.set_attribute(
          "display_name", id2string(symbol.display_name()));
        xml_function.set_attribute("identifier", id2string(step.identifier));
        xml_function.new_element()=xml(symbol.location);

        if(xml_location.name!="")
          xml_call_return.new_element().swap(xml_location);
      }
      break;

    default:
      if(source_location!=previous_source_location)
      {
        // just the source location
        if(xml_location.name!="")
        {
          xmlt &xml_location_only=dest.new_element("location-only");

          xml_location_only.set_attribute_bool("hidden", step.hidden);
          xml_location_only.set_attribute(
            "thread", std::to_string(step.thread_nr));
          xml_location_only.set_attribute(
            "step_nr", std::to_string(step.step_nr));

          xml_location_only.new_element().swap(xml_location);
        }
      }
    }

    if(source_location.is_not_nil() && source_location.get_file()!="")
      previous_source_location=source_location;
  }
}
