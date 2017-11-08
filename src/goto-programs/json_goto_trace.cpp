/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: November 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#include "json_goto_trace.h"

#include <util/json_expr.h>
#include <util/arith_tools.h>
#include <util/config.h>
#include <util/invariant.h>
#include <util/simplify_expr.h>

#include <langapi/language_util.h>

namespace
{
class json_conversion_visitort
  : public defaulted_trace_const_visitor_const_argst
{
public:
  json_conversion_visitort(
    const namespacet &ns,
    const source_locationt &previous_source_location,
    const source_locationt &source_location,
    const jsont &json_location,
    json_arrayt &dest_array)
    : ns_{ns},
      previous_source_location_{previous_source_location},
      source_location_{source_location},
      json_location_{json_location},
      dest_array_{dest_array}
  {
  }

  void default_visit(const goto_trace_stept &step) const override
  {
    if(source_location_ != previous_source_location_)
    {
      // just the source location
      if(!json_location_.is_null())
      {
        json_objectt &json_location_only =
          dest_array_.push_back().make_object();
        json_location_only["stepType"] = json_stringt("location-only");
        json_location_only["hidden"] = jsont::json_boolean(step.hidden);
        json_location_only["internal"] = jsont::json_boolean(step.internal);
        json_location_only["thread"] =
          json_numbert(std::to_string(step.thread_nr));
        json_location_only["sourceLocation"] = json_location_;
      }
    }
  }

  void visit(const trace_assertt &step) const override
  {
    if(!step.cond_value)
    {
      irep_idt property_id;

      if(step.pc->is_assert())
        property_id = source_location_.get_property_id();
      else if(step.pc->is_goto()) // unwinding, we suspect
      {
        property_id = id2string(step.pc->source_location.get_function()) +
                      ".unwind." + std::to_string(step.pc->loop_number);
      }

      json_objectt &json_failure = dest_array_.push_back().make_object();

      json_failure["stepType"] = json_stringt("failure");
      json_failure["hidden"] = jsont::json_boolean(step.hidden);
      json_failure["internal"] = jsont::json_boolean(step.internal);
      json_failure["thread"] = json_numbert(std::to_string(step.thread_nr));
      json_failure["reason"] = json_stringt(id2string(step.comment));
      json_failure["property"] = json_stringt(id2string(property_id));

      if(!json_location_.is_null())
        json_failure["sourceLocation"] = json_location_;
    }
  }

  void visit(const trace_assignmentt &step) const override
  {
    visit_assign_or_decl(step);
  }

  void visit(const trace_declt &step) const override
  {
    visit_assign_or_decl(step);
  }

  void visit(const trace_outputt &step) const override
  {
    json_objectt &json_output = dest_array_.push_back().make_object();

    json_output["stepType"] = json_stringt("output");
    json_output["hidden"] = jsont::json_boolean(step.hidden);
    json_output["internal"] = jsont::json_boolean(step.internal);
    json_output["thread"] = json_numbert(std::to_string(step.thread_nr));
    json_output["outputID"] = json_stringt(id2string(step.io_id));

    // Recovering the mode from the function
    irep_idt mode;
    const symbolt *function_name;
    if(ns_.lookup(source_location_.get_function(), function_name))
      // Failed to find symbol
      mode = ID_unknown;
    else
      mode = function_name->mode;
    json_output["mode"] = json_stringt(id2string(mode));
    json_arrayt &json_values = json_output["values"].make_array();

    for(const auto &arg : step.io_args)
    {
      if(arg.is_nil())
        json_values.push_back(json_stringt(""));
      else
        json_values.push_back(json(arg, ns_, mode));
    }

    if(!json_location_.is_null())
      json_output["sourceLocation"] = json_location_;
  }

  void visit(const trace_inputt &step) const override
  {
    json_objectt &json_input = dest_array_.push_back().make_object();

    json_input["stepType"] = json_stringt("input");
    json_input["hidden"] = jsont::json_boolean(step.hidden);
    json_input["internal"] = jsont::json_boolean(step.internal);
    json_input["thread"] = json_numbert(std::to_string(step.thread_nr));
    json_input["inputID"] = json_stringt(id2string(step.io_id));

    // Recovering the mode from the function
    irep_idt mode;
    const symbolt *function_name;
    if(ns_.lookup(source_location_.get_function(), function_name))
      // Failed to find symbol
      mode = ID_unknown;
    else
      mode = function_name->mode;
    json_input["mode"] = json_stringt(id2string(mode));
    json_arrayt &json_values = json_input["values"].make_array();

    for(const auto &arg : step.io_args)
    {
      if(arg.is_nil())
        json_values.push_back(json_stringt(""));
      else
        json_values.push_back(json(arg, ns_, mode));
    }

    if(!json_location_.is_null())
      json_input["sourceLocation"] = json_location_;
  }

  void visit(const trace_function_callt &step) const override
  {
    visit_function_call_or_return(step);
  }

  void visit(const trace_function_returnt &step) const override
  {
    visit_function_call_or_return(step);
  }

private:
  void visit_assign_or_decl(const goto_trace_stept &step) const
  {
    irep_idt identifier = step.lhs_object.get_identifier();
    json_objectt &json_assignment = dest_array_.push_back().make_object();

    json_assignment["stepType"] = json_stringt("assignment");

    if(!json_location_.is_null())
      json_assignment["sourceLocation"] = json_location_;

    std::string value_string, binary_string, type_string, full_lhs_string;
    json_objectt full_lhs_value;

    DATA_INVARIANT(
      step.full_lhs.is_not_nil(), "full_lhs in assignment must not be nil");
    exprt simplified = simplify_expr(step.full_lhs, ns_);
    full_lhs_string = from_expr(ns_, identifier, simplified);

    const symbolt *symbol;
    irep_idt base_name, display_name;

    if(!ns_.lookup(identifier, symbol))
    {
      base_name = symbol->base_name;
      display_name = symbol->display_name();
      if(type_string == "")
        type_string = from_type(ns_, identifier, symbol->type);

      json_assignment["mode"] = json_stringt(id2string(symbol->mode));
      exprt simplified = simplify_expr(step.full_lhs_value, ns_);

      full_lhs_value = json(simplified, ns_, symbol->mode);
    }
    else
    {
      DATA_INVARIANT(
        step.full_lhs_value.is_not_nil(),
        "full_lhs_value in assignment must not be nil");
      full_lhs_value = json(step.full_lhs_value, ns_, ID_unknown);
    }

    json_assignment["value"] = full_lhs_value;
    json_assignment["lhs"] = json_stringt(full_lhs_string);
    json_assignment["hidden"] = jsont::json_boolean(step.hidden);
    json_assignment["internal"] = jsont::json_boolean(step.internal);
    json_assignment["thread"] = json_numbert(std::to_string(step.thread_nr));

    json_assignment["assignmentType"] = json_stringt(
      step.assignment_type ==
          goto_trace_stept::assignment_typet::ACTUAL_PARAMETER
        ? "actual-parameter"
        : "variable");
  }

  void visit_function_call_or_return(const goto_trace_stept &step) const
  {
    std::string tag =
      step.is_function_call() ? "function-call" : "function-return";
    json_objectt &json_call_return = dest_array_.push_back().make_object();

    json_call_return["stepType"] = json_stringt(tag);
    json_call_return["hidden"] = jsont::json_boolean(step.hidden);
    json_call_return["internal"] = jsont::json_boolean(step.internal);
    json_call_return["thread"] = json_numbert(std::to_string(step.thread_nr));

    const symbolt &symbol = ns_.lookup(step.identifier);
    json_objectt &json_function = json_call_return["function"].make_object();
    json_function["displayName"] =
      json_stringt(id2string(symbol.display_name()));
    json_function["identifier"] = json_stringt(id2string(step.identifier));
    json_function["sourceLocation"] = json(symbol.location);

    if(!json_location_.is_null())
      json_call_return["sourceLocation"] = json_location_;
  }

  const namespacet &ns_;
  const source_locationt &previous_source_location_;
  const source_locationt &source_location_;
  const jsont &json_location_;
  json_arrayt &dest_array_;
};

} // namespace

/// Produce a json representation of a trace.
/// \param ns: a namespace
/// \param goto_trace: a trace in a goto program
/// \param dest: referecence to a json object in which the goto trace will be
///   added
void convert(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  jsont &dest)
{
  json_arrayt &dest_array=dest.make_array();

  source_locationt previous_source_location;

  for(const auto &step : goto_trace.steps)
  {
    const source_locationt &source_location=step->pc->source_location;

    jsont json_location;

    if(source_location.is_not_nil() && source_location.get_file()!="")
      json_location=json(source_location);
    else
      json_location=json_nullt();

    step->accept(
      json_conversion_visitort{ns,
                               previous_source_location,
                               source_location,
                               json_location,
                               dest_array});

    if(source_location.is_not_nil() && source_location.get_file()!="")
      previous_source_location=source_location;
  }
}
