/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: November 2005

\*******************************************************************/

#include <cassert>

#include <util/i2string.h>

#include <langapi/language_util.h>

#include "json_goto_trace.h"

/*******************************************************************\

Function: json

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

jsont json(const source_locationt &source_location)
{
  jsont result=jsont::json_object();

  if(!source_location.get_file().empty())
    result["file"]=jsont(id2string(source_location.get_file()));

  if(!source_location.get_line().empty())
    result["line"]=jsont::json_number(id2string(source_location.get_line()));

  if(!source_location.get_column().empty())
    result["column"]=jsont::json_number(id2string(source_location.get_column()));

  if(!source_location.get_function().empty())
    result["function"]=jsont(id2string(source_location.get_function()));
    
  return result;
}

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
  dest=jsont::json_array();
  
  source_locationt previous_source_location;

  for(goto_tracet::stepst::const_iterator
      it=goto_trace.steps.begin();
      it!=goto_trace.steps.end();
      it++)
  {
    const source_locationt &source_location=it->pc->source_location;

    jsont json_location;

    if(source_location.is_not_nil() && source_location.get_file()!="")
      json_location=json(source_location);
    else
      json_location=jsont::json_null();
    
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
      
        jsont &json_failure=dest.push_back(jsont::json_object());
        
        json_failure["step_type"]=jsont("failure");
        json_failure["hidden"]=jsont::json_boolean(it->hidden);
        json_failure["thread"]=jsont::json_number(i2string(it->thread_nr));
        json_failure["reason"]=jsont(id2string(it->comment));
        json_failure["property"]=jsont(id2string(property_id));

        if(!json_location.is_null())
          json_failure["source_location"]=json_location;
      }
      break;
      
    case goto_trace_stept::ASSIGNMENT:
    case goto_trace_stept::DECL:
      {
        irep_idt identifier=it->lhs_object.get_identifier();
        jsont &json_assignment=dest.push_back(jsont::json_object());
        
        json_assignment["step_type"]=jsont("assignment");

        if(!json_location.is_null())
          json_assignment["source_location"]=json_location;

        std::string value_string, binary_string, type_string,
                    full_lhs_string, full_lhs_value_string;
        
        //if(it->lhs_object_value.is_not_nil())
        //  value_string=from_expr(ns, identifier, it->lhs_object_value);

        if(it->full_lhs.is_not_nil())
          full_lhs_string=from_expr(ns, identifier, it->full_lhs);

        if(it->full_lhs_value.is_not_nil())
          full_lhs_value_string=from_expr(ns, identifier, it->full_lhs_value);

        //if(it->lhs_object_value.type().is_not_nil())
        //  type_string=from_type(ns, identifier, it->lhs_object_value.type());

        const symbolt *symbol;
        irep_idt base_name, display_name;

        if(!ns.lookup(identifier, symbol))
        {
          base_name=symbol->base_name;
          display_name=symbol->display_name();
          if(type_string=="")
            type_string=from_type(ns, identifier, symbol->type);

          json_assignment["mode"]=jsont(id2string(symbol->mode));
        }

        json_assignment["value"]=jsont(full_lhs_value_string);
        json_assignment["lhs"]=jsont(full_lhs_string);
        json_assignment["hidden"]=jsont::json_boolean(it->hidden);
        json_assignment["thread"]=jsont::json_number(i2string(it->thread_nr));

        json_assignment["assignment_type"]=
          jsont(it->assignment_type==goto_trace_stept::ACTUAL_PARAMETER?"actual_parameter":
                "variable");
      }
      break;
      
    case goto_trace_stept::OUTPUT:
      // TODO
      break;
      
    case goto_trace_stept::INPUT:
      // TODO
      break;
      
    case goto_trace_stept::FUNCTION_CALL:
    case goto_trace_stept::FUNCTION_RETURN:
      {
        std::string tag=
          (it->type==goto_trace_stept::FUNCTION_CALL)?"function_call":"function_return";
        jsont &json_call_return=dest.push_back(jsont::json_object());
        
        json_call_return["step_type"]=jsont(tag);
        json_call_return["hidden"]=jsont::json_boolean(it->hidden);
        json_call_return["thread"]=jsont::json_number(i2string(it->thread_nr));

        const symbolt &symbol=ns.lookup(it->identifier);
        jsont &json_function=json_call_return["function"];
        json_function=jsont::json_object();
        json_function["display_name"]=jsont(id2string(symbol.display_name()));
        json_function["identifier"]=jsont(id2string(it->identifier));
        json_function["source_location"]=json(symbol.location);

        if(!json_location.is_null())
          json_call_return["source_location"]=json_location;
      }
      break;
      
    default:
      if(source_location!=previous_source_location)
      {
        // just the source location
        if(!json_location.is_null())
        {
          jsont &json_location_only=dest["location-only"];
          json_location_only["hidden"]=jsont::json_boolean(it->hidden);
          json_location_only["thread"]=jsont::json_number(i2string(it->thread_nr));
          json_location_only["source_location"]=json_location;
        }
      }
    }

    if(source_location.is_not_nil() && source_location.get_file()!="")
      previous_source_location=source_location;
  }
}
