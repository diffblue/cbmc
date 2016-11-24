/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: November 2005

\*******************************************************************/

#include <cassert>

#include <util/xml_expr.h>
#include <util/i2string.h>
#include <util/symbol.h>

#include <ansi-c/printf_formatter.h>
#include <langapi/language_util.h>

#include "xml_goto_trace.h"

/*******************************************************************\

Function: convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  xmlt &dest)
{
  dest=xmlt("goto_trace");
  
  source_locationt previous_source_location;

  for(goto_tracet::stepst::const_iterator
      it=goto_trace.steps.begin();
      it!=goto_trace.steps.end();
      it++)
  {
    const source_locationt &source_location=it->pc->source_location;

    xmlt xml_location;
    if(source_location.is_not_nil() && source_location.get_file()!="")
      xml_location=xml(source_location);
    
    switch(it->type)
    {
    case goto_trace_stept::ASSERT:
      if(!it->cond_value)
      {
        irep_idt property_id;
        
        if(it->pc->is_assert())
          property_id=source_location.get_property_id();
        else if(it->pc->is_goto()) // unwinding, we suspect
        {
          property_id=
            id2string(it->pc->source_location.get_function())+".unwind."+
            i2string(it->pc->loop_number);
        }
      
        xmlt &xml_failure=dest.new_element("failure");

        xml_failure.set_attribute_bool("hidden", it->hidden);
        xml_failure.set_attribute("thread", i2string(it->thread_nr));
        xml_failure.set_attribute("step_nr", i2string(it->step_nr));
        xml_failure.set_attribute("reason", id2string(it->comment));
        xml_failure.set_attribute("property", id2string(property_id));

        if(xml_location.name!="")
          xml_failure.new_element().swap(xml_location);
      }
      break;
      
    case goto_trace_stept::ASSIGNMENT:
    case goto_trace_stept::DECL:
      {
        irep_idt identifier=it->lhs_object.get_identifier();
        xmlt &xml_assignment=dest.new_element("assignment");

        if(xml_location.name!="")
          xml_assignment.new_element().swap(xml_location);

        std::string value_string, binary_string, type_string,
                    full_lhs_string, full_lhs_value_string;
        
        if(it->lhs_object_value.is_not_nil())
          value_string=from_expr(ns, identifier, it->lhs_object_value);

        if(it->full_lhs.is_not_nil())
          full_lhs_string=from_expr(ns, identifier, it->full_lhs);

        if(it->full_lhs_value.is_not_nil())
          full_lhs_value_string=from_expr(ns, identifier, it->full_lhs_value);

        if(it->lhs_object_value.type().is_not_nil())
          type_string=from_type(ns, identifier, it->lhs_object_value.type());

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
        
        xml_assignment.set_attribute_bool("hidden", it->hidden);
        xml_assignment.set_attribute("thread", i2string(it->thread_nr));
        xml_assignment.set_attribute("identifier", id2string(identifier));
        xml_assignment.set_attribute("base_name", id2string(base_name));
        xml_assignment.set_attribute("display_name", id2string(display_name));
        xml_assignment.set_attribute("step_nr", i2string(it->step_nr));

        xml_assignment.set_attribute("assignment_type", 
          it->assignment_type==goto_trace_stept::ACTUAL_PARAMETER?"actual_parameter":
          "state");

        if(it->lhs_object_value.is_not_nil())
          xml_assignment.new_element("value_expression").new_element(xml(it->lhs_object_value, ns));
      }
      break;
      
    case goto_trace_stept::OUTPUT:
      {
        printf_formattert printf_formatter(ns);
        printf_formatter(id2string(it->format_string), it->io_args);
        std::string text=printf_formatter.as_string();
        xmlt &xml_output=dest.new_element("output");
        
        xml_output.new_element("text").data=text;

        xml_output.set_attribute_bool("hidden", it->hidden);
        xml_output.set_attribute("thread", i2string(it->thread_nr));
        xml_output.set_attribute("step_nr", i2string(it->step_nr));

        if(xml_location.name!="")
          xml_output.new_element().swap(xml_location);

        for(std::list<exprt>::const_iterator
            l_it=it->io_args.begin();
            l_it!=it->io_args.end();
            l_it++)
        {
          xml_output.new_element("value").data=from_expr(ns, "", *l_it);
          xml_output.new_element("value_expression").
            new_element(xml(*l_it, ns));
        }
      }
      break;
      
    case goto_trace_stept::INPUT:
      {
        xmlt &xml_input=dest.new_element("input");
        xml_input.new_element("input_id").data=id2string(it->io_id);
        
        xml_input.set_attribute_bool("hidden", it->hidden);
        xml_input.set_attribute("thread", i2string(it->thread_nr));
        xml_input.set_attribute("step_nr", i2string(it->step_nr));
        
        for(std::list<exprt>::const_iterator
            l_it=it->io_args.begin();
            l_it!=it->io_args.end();
            l_it++)
        {
          xml_input.new_element("value").data=from_expr(ns, "", *l_it);
          xml_input.new_element("value_expression").
            new_element(xml(*l_it, ns));
        }
            
        if(xml_location.name!="")
          xml_input.new_element().swap(xml_location);
      }
      break;
      
    case goto_trace_stept::FUNCTION_CALL:
    case goto_trace_stept::FUNCTION_RETURN:
      {
        std::string tag=
          (it->type==goto_trace_stept::FUNCTION_CALL)?"function_call":"function_return";
        xmlt &xml_call_return=dest.new_element(tag);
        
        xml_call_return.set_attribute_bool("hidden", it->hidden);
        xml_call_return.set_attribute("thread", i2string(it->thread_nr));
        xml_call_return.set_attribute("step_nr", i2string(it->step_nr));

        const symbolt &symbol=ns.lookup(it->identifier);
        xmlt &xml_function=xml_call_return.new_element("function");
        xml_function.set_attribute("display_name", id2string(symbol.display_name()));
        xml_function.set_attribute("identifier", id2string(it->identifier));
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
          
          xml_location_only.set_attribute_bool("hidden", it->hidden);
          xml_location_only.set_attribute("thread", i2string(it->thread_nr));
          xml_location_only.set_attribute("step_nr", i2string(it->step_nr));

          xml_location_only.new_element().swap(xml_location);
        }
      }
    }

    if(source_location.is_not_nil() && source_location.get_file()!="")
      previous_source_location=source_location;
  }
}
