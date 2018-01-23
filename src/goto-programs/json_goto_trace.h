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

/// Produce a json representation of a trace.
/// \param ns: a namespace
/// \param goto_trace: a trace in a goto program
/// \param dest: referecence to a json stream in which the goto trace will be
///   added
template<class json_arrayT>
void convert(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  json_arrayT &dest_array,
  trace_optionst trace_options = trace_optionst::default_options)
{
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

        DATA_INVARIANT(
          step.full_lhs.is_not_nil(),
          "full_lhs in assignment must not be nil");
        exprt simplified=simplify_expr(step.full_lhs, ns);

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
                const symbolt &symbol = ns.lookup(expr.get(ID_identifier));
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

        full_lhs_string=from_expr(ns, identifier, simplified);

        const symbolt *symbol;
        irep_idt base_name, display_name;

        if(!ns.lookup(identifier, symbol))
        {
          base_name=symbol->base_name;
          display_name=symbol->display_name();
          if(type_string=="")
            type_string=from_type(ns, identifier, symbol->type);

          json_assignment["mode"]=json_stringt(id2string(symbol->mode));
          exprt simplified=simplify_expr(step.full_lhs_value, ns);

          full_lhs_value=json(simplified, ns, symbol->mode);
        }
        else
        {
          DATA_INVARIANT(
            step.full_lhs_value.is_not_nil(),
            "full_lhs_value in assignment must not be nil");
          full_lhs_value=json(step.full_lhs_value, ns, ID_unknown);
        }

        json_assignment["value"]=full_lhs_value;
        json_assignment["lhs"]=json_stringt(full_lhs_string);
        if(trace_options.json_full_lhs)
        {
          // Not language specific, still mangled, fully-qualified name of lhs
          json_assignment["rawLhs"] =
            json_irept(true).convert_from_irep(simplified);
        }
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

        // Recovering the mode from the function
        irep_idt mode;
        const symbolt *function_name;
        if(ns.lookup(source_location.get_function(), function_name))
          // Failed to find symbol
          mode=ID_unknown;
        else
          mode=function_name->mode;
        json_output["mode"]=json_stringt(id2string(mode));
        json_arrayt &json_values=json_output["values"].make_array();

        for(const auto &arg : step.io_args)
        {
          if(arg.is_nil())
            json_values.push_back(json_stringt(""));
          else
            json_values.push_back(json(arg, ns, mode));
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

        // Recovering the mode from the function
        irep_idt mode;
        const symbolt *function_name;
        if(ns.lookup(source_location.get_function(), function_name))
          // Failed to find symbol
          mode=ID_unknown;
        else
          mode=function_name->mode;
        json_input["mode"]=json_stringt(id2string(mode));
        json_arrayt &json_values=json_input["values"].make_array();

        for(const auto &arg : step.io_args)
        {
          if(arg.is_nil())
            json_values.push_back(json_stringt(""));
          else
            json_values.push_back(json(arg, ns, mode));
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

#endif // CPROVER_GOTO_PROGRAMS_JSON_GOTO_TRACE_H
