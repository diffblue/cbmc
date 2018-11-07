/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: November 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#include "json_goto_trace.h"
#include "goto_trace.h"

#include <util/json_expr.h>
#include <util/json.h>
#include <util/json_stream.h>
#include <util/arith_tools.h>
#include <util/config.h>
#include <util/invariant.h>
#include <util/simplify_expr.h>
#include <util/json_irep.h>
#include <langapi/language_util.h>

/// Convert an ASSERT goto_trace step.
/// \param [out] json_failure: The JSON object that
///   will contain the information about the step
///   after this function has run.
/// \param conversion_dependencies: A structure
///   that contains information the conversion function
///   needs.
void convert_assert(
  json_objectt &json_failure,
  const conversion_dependenciest &conversion_dependencies)
{
  const goto_trace_stept &step = conversion_dependencies.step;
  const jsont &location = conversion_dependencies.location;
  const source_locationt &source_location =
    conversion_dependencies.source_location;

  irep_idt property_id =
    step.pc->is_assert()
      ? source_location.get_property_id()
      : step.pc->is_goto()
          ? id2string(step.pc->source_location.get_function()) + ".unwind." +
              std::to_string(step.pc->loop_number)
          : "";

  json_failure["stepType"] = json_stringt("failure");
  json_failure["hidden"] = jsont::json_boolean(step.hidden);
  json_failure["internal"] = jsont::json_boolean(step.internal);
  json_failure["thread"] = json_numbert(std::to_string(step.thread_nr));
  json_failure["reason"] = json_stringt(step.comment);
  json_failure["property"] = json_stringt(property_id);

  if(!location.is_null())
    json_failure["sourceLocation"] = location;
}

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
  const trace_optionst &trace_options)
{
  const goto_trace_stept &step = conversion_dependencies.step;
  const jsont &json_location = conversion_dependencies.location;
  const namespacet &ns = conversion_dependencies.ns;

  auto lhs_object=step.get_lhs_object();

  irep_idt identifier =
    lhs_object.has_value()?lhs_object->get_identifier():irep_idt();

  json_assignment["stepType"] = json_stringt("assignment");

  if(!json_location.is_null())
    json_assignment["sourceLocation"] = json_location;

  std::string value_string, type_string, full_lhs_string;
  json_objectt full_lhs_value;

  DATA_INVARIANT(
    step.full_lhs.is_not_nil(), "full_lhs in assignment must not be nil");
  exprt simplified = simplify_expr(step.full_lhs, ns);

  if(trace_options.json_full_lhs)
  {
    class comment_base_name_visitort : public expr_visitort
    {
    private:
      const namespacet &ns;

    public:
      explicit comment_base_name_visitort(const namespacet &ns) : ns(ns)
      {
      }

      void operator()(exprt &expr) override
      {
        if(expr.id() == ID_symbol)
        {
          const symbolt &symbol = ns.lookup(to_symbol_expr(expr));

          if(expr.find(ID_C_base_name).is_not_nil())
            INVARIANT(
              expr.find(ID_C_base_name).id() == symbol.base_name,
              "base_name comment does not match symbol's base_name");
          else
            expr.add(ID_C_base_name, irept(symbol.base_name));
        }
      }
    };
    comment_base_name_visitort comment_base_name_visitor(ns);
    simplified.visit(comment_base_name_visitor);
  }

  full_lhs_string = from_expr(ns, identifier, simplified);

  const symbolt *symbol;
  irep_idt base_name, display_name;

  if(!ns.lookup(identifier, symbol))
  {
    base_name = symbol->base_name;
    display_name = symbol->display_name();
    if(type_string == "")
      type_string = from_type(ns, identifier, symbol->type);

    json_assignment["mode"] = json_stringt(symbol->mode);
    exprt simplified = simplify_expr(step.full_lhs_value, ns);

    full_lhs_value = json(simplified, ns, symbol->mode);
  }
  else
  {
    DATA_INVARIANT(
      step.full_lhs_value.is_not_nil(),
      "full_lhs_value in assignment must not be nil");
    full_lhs_value = json(step.full_lhs_value, ns, ID_unknown);
  }

  json_assignment["value"] = full_lhs_value;
  json_assignment["lhs"] = json_stringt(full_lhs_string);
  if(trace_options.json_full_lhs)
  {
    // Not language specific, still mangled, fully-qualified name of lhs
    json_assignment["rawLhs"] = json_irept(true).convert_from_irep(simplified);
  }
  json_assignment["hidden"] = jsont::json_boolean(step.hidden);
  json_assignment["internal"] = jsont::json_boolean(step.internal);
  json_assignment["thread"] = json_numbert(std::to_string(step.thread_nr));

  json_assignment["assignmentType"] = json_stringt(
    step.assignment_type == goto_trace_stept::assignment_typet::ACTUAL_PARAMETER
      ? "actual-parameter"
      : "variable");
}

/// Convert an OUTPUT goto_trace step.
/// \param [out] json_output: The JSON object that
///   will contain the information about the step
///   after this function has run.
/// \param conversion_dependencies: A structure
///   that contains information the conversion function
///   needs.
void convert_output(
  json_objectt &json_output,
  const conversion_dependenciest &conversion_dependencies)
{
  const goto_trace_stept &step = conversion_dependencies.step;
  const jsont &location = conversion_dependencies.location;
  const namespacet &ns = conversion_dependencies.ns;
  const source_locationt &source_location = step.pc->source_location;

  json_output["stepType"] = json_stringt("output");
  json_output["hidden"] = jsont::json_boolean(step.hidden);
  json_output["internal"] = jsont::json_boolean(step.internal);
  json_output["thread"] = json_numbert(std::to_string(step.thread_nr));
  json_output["outputID"] = json_stringt(step.io_id);

  // Recovering the mode from the function
  irep_idt mode;
  const symbolt *function_name;
  if(ns.lookup(source_location.get_function(), function_name))
    // Failed to find symbol
    mode = ID_unknown;
  else
    mode = function_name->mode;
  json_output["mode"] = json_stringt(mode);
  json_arrayt &json_values = json_output["values"].make_array();

  for(const auto &arg : step.io_args)
  {
    arg.is_nil() ? json_values.push_back(json_stringt(""))
                 : json_values.push_back(json(arg, ns, mode));
  }

  if(!location.is_null())
    json_output["sourceLocation"] = location;
}

/// Convert an INPUT goto_trace step.
/// \param [out] json_input: The JSON object that
///   will contain the information about the step
///   after this function has run.
/// \param conversion_dependencies: A structure
///   that contains information the conversion function
///   needs.
void convert_input(
  json_objectt &json_input,
  const conversion_dependenciest &conversion_dependencies)
{
  const goto_trace_stept &step = conversion_dependencies.step;
  const jsont &location = conversion_dependencies.location;
  const namespacet &ns = conversion_dependencies.ns;
  const source_locationt &source_location = step.pc->source_location;

  json_input["stepType"] = json_stringt("input");
  json_input["hidden"] = jsont::json_boolean(step.hidden);
  json_input["internal"] = jsont::json_boolean(step.internal);
  json_input["thread"] = json_numbert(std::to_string(step.thread_nr));
  json_input["inputID"] = json_stringt(step.io_id);

  // Recovering the mode from the function
  irep_idt mode;
  const symbolt *function_name;
  if(ns.lookup(source_location.get_function(), function_name))
    // Failed to find symbol
    mode = ID_unknown;
  else
    mode = function_name->mode;
  json_input["mode"] = json_stringt(mode);
  json_arrayt &json_values = json_input["values"].make_array();

  for(const auto &arg : step.io_args)
  {
    arg.is_nil() ? json_values.push_back(json_stringt(""))
                 : json_values.push_back(json(arg, ns, mode));
  }

  if(!location.is_null())
    json_input["sourceLocation"] = location;
}

/// Convert a FUNCTION_RETURN goto_trace step.
/// \param [out] json_call_return: The JSON object that
///   will contain the information about the step
///   after this function has run.
/// \param conversion_dependencies: A structure
///   that contains information the conversion function
///   needs.
void convert_return(
  json_objectt &json_call_return,
  const conversion_dependenciest &conversion_dependencies)
{
  const goto_trace_stept &step = conversion_dependencies.step;
  const jsont &location = conversion_dependencies.location;
  const namespacet &ns = conversion_dependencies.ns;

  std::string tag = (step.type == goto_trace_stept::typet::FUNCTION_CALL)
                      ? "function-call"
                      : "function-return";

  json_call_return["stepType"] = json_stringt(tag);
  json_call_return["hidden"] = jsont::json_boolean(step.hidden);
  json_call_return["internal"] = jsont::json_boolean(step.internal);
  json_call_return["thread"] = json_numbert(std::to_string(step.thread_nr));

  const irep_idt &function_identifier =
    (step.type == goto_trace_stept::typet::FUNCTION_CALL) ? step.called_function
                                                          : step.function;

  const symbolt &symbol = ns.lookup(function_identifier);
  json_objectt &json_function = json_call_return["function"].make_object();
  json_function["displayName"] = json_stringt(symbol.display_name());
  json_function["identifier"] = json_stringt(function_identifier);
  json_function["sourceLocation"] = json(symbol.location);

  if(!location.is_null())
    json_call_return["sourceLocation"] = location;
}

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
  const conversion_dependenciest &conversion_dependencies)
{
  const goto_trace_stept &step = conversion_dependencies.step;
  const jsont &location = conversion_dependencies.location;

  json_location_only["stepType"] = json_stringt("location-only");
  json_location_only["hidden"] = jsont::json_boolean(step.hidden);
  json_location_only["thread"] = json_numbert(std::to_string(step.thread_nr));
  json_location_only["sourceLocation"] = location;
}
