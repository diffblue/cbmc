/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: November 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#include <cassert>

#include <util/json_expr.h>

#include <langapi/language_util.h>

#include "json_goto_trace.h"

void convert_assert(json_objectt &json_failure,
 conversion_dependenciest &conversion_dependencies)
{
  const goto_trace_stept& step=conversion_dependencies.step;
  jsont &location=conversion_dependencies.location;
  const source_locationt &source_location=conversion_dependencies.source_location;

  irep_idt property_id = step.pc->is_assert()? 
    source_location.get_property_id(): 
    step.pc->is_goto()?  
    id2string(step.pc->source_location.get_function())+
    ".unwind."+std::to_string(step.pc->loop_number):
    "";

  json_failure["stepType"]=json_stringt("failure");
  json_failure["hidden"]=jsont::json_boolean(step.hidden);
  json_failure["thread"]=json_numbert(std::to_string(step.thread_nr));
  json_failure["reason"]=json_stringt(id2string(step.comment));
  json_failure["property"]=json_stringt(id2string(property_id));

  if(!location.is_null())
    json_failure["sourceLocation"]=location;
}

void convert_decl(json_objectt &json_assignment,
  conversion_dependenciest &conversion_dependencies)
{
  const goto_trace_stept& step=conversion_dependencies.step;
  jsont &location=conversion_dependencies.location;
  const namespacet &ns=conversion_dependencies.ns;

  irep_idt identifier=step.lhs_object.get_identifier();

  json_assignment["stepType"]=json_stringt("assignment");

  if(!location.is_null())
    json_assignment["sourceLocation"]=location;

  std::string value_string, binary_string, type_string, full_lhs_string;
  json_objectt full_lhs_value;

  if(step.full_lhs.is_not_nil())
    full_lhs_string=from_expr(ns, identifier, step.full_lhs);

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
  json_assignment["thread"]=json_numbert(std::to_string(step.thread_nr));

  json_assignment["assignmentType"]=
  json_stringt(
    step.assignment_type==
    goto_trace_stept::assignment_typet::ACTUAL_PARAMETER?
    "actual-parameter":
    "variable");
}


void convert_output(json_objectt &json_output,
  conversion_dependenciest &conversion_dependencies)
{
  const goto_trace_stept& step=conversion_dependencies.step;
  jsont &location=conversion_dependencies.location;
  const namespacet &ns=conversion_dependencies.ns;

  json_output["stepType"]=json_stringt("output");
  json_output["hidden"]=jsont::json_boolean(step.hidden);
  json_output["thread"]=json_numbert(std::to_string(step.thread_nr));
  json_output["outputID"]=json_stringt(id2string(step.io_id));

  json_arrayt &json_values=json_output["values"].make_array();

  for(const auto &arg : step.io_args)
  {
    arg.is_nil()? 
    json_values.push_back(json_stringt("")):
    json_values.push_back(json(arg, ns));
  }

  if(!location.is_null())
    json_output["sourceLocation"]=location;
}

void convert_input(json_objectt &json_input,
  conversion_dependenciest &conversion_dependencies)
{
  const goto_trace_stept& step=conversion_dependencies.step;
  jsont &location=conversion_dependencies.location;
  const namespacet &ns=conversion_dependencies.ns;

  json_input["stepType"]=json_stringt("input");
  json_input["hidden"]=jsont::json_boolean(step.hidden);
  json_input["thread"]=json_numbert(std::to_string(step.thread_nr));
  json_input["inputID"]=json_stringt(id2string(step.io_id));

  json_arrayt &json_values=json_input["values"].make_array();

  for(const auto &arg : step.io_args)
  {
    arg.is_nil()? 
    json_values.push_back(json_stringt("")):
    json_values.push_back(json(arg, ns));
  }

  if(!location.is_null())
    json_input["sourceLocation"]=location;

}

void convert_return(json_objectt &json_call_return,
  conversion_dependenciest &conversion_dependencies)
{
  const goto_trace_stept& step=conversion_dependencies.step;
  jsont &location=conversion_dependencies.location;
  const namespacet &ns=conversion_dependencies.ns;

  std::string tag= (step.type==goto_trace_stept::typet::FUNCTION_CALL)?
    "function-call" : "function-return";

  json_call_return["stepType"]=json_stringt(tag);
  json_call_return["hidden"]=jsont::json_boolean(step.hidden);
  json_call_return["thread"]=json_numbert(std::to_string(step.thread_nr));

  const symbolt &symbol=ns.lookup(step.identifier);
  json_objectt &json_function=json_call_return["function"].make_object();
  json_function["displayName"]=
  json_stringt(id2string(symbol.display_name()));
  json_function["identifier"]=json_stringt(id2string(step.identifier));
  json_function["sourceLocation"]=json(symbol.location);

  if(!location.is_null())
    json_call_return["sourceLocation"]=location;
}

void convert_default(json_objectt &json_location_only,
  conversion_dependenciest &conversion_dependencies)
{
  const goto_trace_stept& step=conversion_dependencies.step;
  jsont &location=conversion_dependencies.location;

  json_location_only["stepType"]=json_stringt("location-only");
  json_location_only["hidden"]=jsont::json_boolean(step.hidden);
  json_location_only["thread"]=json_numbert(std::to_string(step.thread_nr));
  json_location_only["sourceLocation"]=location;
}
