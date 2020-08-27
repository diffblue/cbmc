/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: November 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#include "xml_goto_trace.h"

#include <cassert>

#include <util/symbol.h>
#include <util/xml_irep.h>

#include <langapi/language_util.h>
#include <util/arith_tools.h>

#include "printf_formatter.h"
#include "structured_trace_util.h"
#include "xml_expr.h"

xmlt full_lhs_value(const goto_trace_stept &step, const namespacet &ns)
{
  xmlt value_xml{"full_lhs_value"};

  const exprt &value = step.full_lhs_value;
  if(value.is_nil())
    return value_xml;

  const auto &lhs_object = step.get_lhs_object();
  const irep_idt identifier =
    lhs_object.has_value() ? lhs_object->get_identifier() : irep_idt();
  value_xml.data = from_expr(ns, identifier, value);

  const auto &bv_type = type_try_dynamic_cast<bitvector_typet>(value.type());
  const auto &constant = expr_try_dynamic_cast<constant_exprt>(value);
  if(bv_type && constant)
  {
    const auto width = bv_type->get_width();
    // It is fine to pass `false` into the `is_signed` parameter, even for
    // signed values, because the subsequent conversion to binary will result
    // in the same value either way. E.g. if the value is `-1` for a signed 8
    // bit value, this will convert to `255` which is `11111111` in binary,
    // which is the desired result.
    const auto binary_representation =
      integer2binary(bvrep2integer(constant->get_value(), width, false), width);
    value_xml.set_attribute("binary", binary_representation);
  }
  return value_xml;
}

void convert(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  xmlt &dest)
{
  dest=xmlt("goto_trace");

  source_locationt previous_source_location;

  for(const auto &step : goto_trace.steps)
  {
    const source_locationt &source_location=step.pc->source_location;

    xmlt xml_location;
    if(source_location.is_not_nil() && !source_location.get_file().empty())
      xml_location=xml(source_location);

    switch(step.type)
    {
    case goto_trace_stept::typet::ASSERT:
      if(!step.cond_value)
      {
        xmlt &xml_failure=dest.new_element("failure");

        xml_failure.set_attribute_bool("hidden", step.hidden);
        xml_failure.set_attribute("thread", std::to_string(step.thread_nr));
        xml_failure.set_attribute("step_nr", std::to_string(step.step_nr));
        xml_failure.set_attribute("reason", id2string(step.comment));
        xml_failure.set_attribute("property", id2string(step.property_id));

        if(!xml_location.name.empty())
          xml_failure.new_element().swap(xml_location);
      }
      break;

    case goto_trace_stept::typet::ASSIGNMENT:
    case goto_trace_stept::typet::DECL:
    {
      auto lhs_object = step.get_lhs_object();
      irep_idt identifier =
        lhs_object.has_value() ? lhs_object->get_identifier() : irep_idt();
      xmlt &xml_assignment = dest.new_element("assignment");

      if(!xml_location.name.empty())
        xml_assignment.new_element().swap(xml_location);

      {
        const symbolt *symbol;

        if(
          lhs_object.has_value() &&
          !ns.lookup(lhs_object->get_identifier(), symbol))
        {
          std::string type_string = from_type(ns, symbol->name, symbol->type);

          xml_assignment.set_attribute("mode", id2string(symbol->mode));
          xml_assignment.set_attribute("identifier", id2string(symbol->name));
          xml_assignment.set_attribute(
            "base_name", id2string(symbol->base_name));
          xml_assignment.set_attribute(
            "display_name", id2string(symbol->display_name()));
          xml_assignment.new_element("type").data = type_string;
        }
      }

      std::string full_lhs_string;

      if(step.full_lhs.is_not_nil())
        full_lhs_string = from_expr(ns, identifier, step.full_lhs);

      xml_assignment.new_element("full_lhs").data = full_lhs_string;
      xml_assignment.new_element(full_lhs_value(step, ns));

      xml_assignment.set_attribute_bool("hidden", step.hidden);
      xml_assignment.set_attribute("thread", std::to_string(step.thread_nr));
      xml_assignment.set_attribute("step_nr", std::to_string(step.step_nr));

      xml_assignment.set_attribute(
        "assignment_type",
        step.assignment_type ==
            goto_trace_stept::assignment_typet::ACTUAL_PARAMETER
          ? "actual_parameter"
          : "state");
      break;
    }

    case goto_trace_stept::typet::OUTPUT:
    {
      printf_formattert printf_formatter(ns);
      printf_formatter(id2string(step.format_string), step.io_args);
      std::string text = printf_formatter.as_string();
      xmlt &xml_output = dest.new_element("output");

      xml_output.new_element("text").data = text;

      xml_output.set_attribute_bool("hidden", step.hidden);
      xml_output.set_attribute("thread", std::to_string(step.thread_nr));
      xml_output.set_attribute("step_nr", std::to_string(step.step_nr));

      if(!xml_location.name.empty())
        xml_output.new_element().swap(xml_location);

      for(const auto &arg : step.io_args)
      {
        xml_output.new_element("value").data =
          from_expr(ns, step.function_id, arg);
        xml_output.new_element("value_expression").new_element(xml(arg, ns));
      }
      break;
    }

    case goto_trace_stept::typet::INPUT:
    {
      xmlt &xml_input = dest.new_element("input");
      xml_input.new_element("input_id").data = id2string(step.io_id);

      xml_input.set_attribute_bool("hidden", step.hidden);
      xml_input.set_attribute("thread", std::to_string(step.thread_nr));
      xml_input.set_attribute("step_nr", std::to_string(step.step_nr));

      for(const auto &arg : step.io_args)
      {
        xml_input.new_element("value").data =
          from_expr(ns, step.function_id, arg);
        xml_input.new_element("value_expression").new_element(xml(arg, ns));
      }

      if(!xml_location.name.empty())
        xml_input.new_element().swap(xml_location);
      break;
    }

    case goto_trace_stept::typet::FUNCTION_CALL:
    {
      std::string tag = "function_call";
      xmlt &xml_call_return = dest.new_element(tag);

      xml_call_return.set_attribute_bool("hidden", step.hidden);
      xml_call_return.set_attribute("thread", std::to_string(step.thread_nr));
      xml_call_return.set_attribute("step_nr", std::to_string(step.step_nr));

      const symbolt &symbol = ns.lookup(step.called_function);
      xmlt &xml_function = xml_call_return.new_element("function");
      xml_function.set_attribute(
        "display_name", id2string(symbol.display_name()));
      xml_function.set_attribute("identifier", id2string(symbol.name));
      xml_function.new_element() = xml(symbol.location);

      if(!xml_location.name.empty())
        xml_call_return.new_element().swap(xml_location);
      break;
    }

    case goto_trace_stept::typet::FUNCTION_RETURN:
    {
      std::string tag = "function_return";
      xmlt &xml_call_return = dest.new_element(tag);

      xml_call_return.set_attribute_bool("hidden", step.hidden);
      xml_call_return.set_attribute("thread", std::to_string(step.thread_nr));
      xml_call_return.set_attribute("step_nr", std::to_string(step.step_nr));

      const symbolt &symbol = ns.lookup(step.called_function);
      xmlt &xml_function = xml_call_return.new_element("function");
      xml_function.set_attribute(
        "display_name", id2string(symbol.display_name()));
      xml_function.set_attribute("identifier", id2string(symbol.name));
      xml_function.new_element() = xml(symbol.location);

      if(!xml_location.name.empty())
        xml_call_return.new_element().swap(xml_location);
      break;
    }

    case goto_trace_stept::typet::ATOMIC_BEGIN:
    case goto_trace_stept::typet::ATOMIC_END:
    case goto_trace_stept::typet::MEMORY_BARRIER:
    case goto_trace_stept::typet::SPAWN:
    case goto_trace_stept::typet::SHARED_WRITE:
    case goto_trace_stept::typet::SHARED_READ:
    case goto_trace_stept::typet::CONSTRAINT:
    case goto_trace_stept::typet::DEAD:
    case goto_trace_stept::typet::LOCATION:
    case goto_trace_stept::typet::GOTO:
    case goto_trace_stept::typet::ASSUME:
    case goto_trace_stept::typet::NONE:
    {
      const auto default_step = ::default_step(step, previous_source_location);
      if(default_step)
      {
        xmlt &xml_location_only =
          dest.new_element(default_step_name(default_step->kind));

        xml_location_only.set_attribute_bool("hidden", default_step->hidden);
        xml_location_only.set_attribute(
          "thread", std::to_string(default_step->thread_number));
        xml_location_only.set_attribute(
          "step_nr", std::to_string(default_step->step_number));

        xml_location_only.new_element(xml(default_step->location));
      }

      break;
    }
    }

    if(source_location.is_not_nil() && !source_location.get_file().empty())
      previous_source_location=source_location;
  }
}
