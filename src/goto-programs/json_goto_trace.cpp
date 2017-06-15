/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: November 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#include "json_goto_trace.h"

#include <cassert>

#include <util/arith_tools.h>
#include <util/json_expr.h>

#include <langapi/language_util.h>

/// Replaces in src, expressions of the form pointer_offset(constant) by that
/// constant.
/// \param src: an expression
void remove_pointer_offsets(exprt &src)
{
  if(src.id()==ID_pointer_offset && src.op0().id()==ID_constant)
    src=src.op0();
  else
    for(auto &op : src.operands())
      remove_pointer_offsets(op);
}

/// Replaces in src, expressions of the form pointer_offset(array_symbol) by a
/// constant value of 0. This is meant to simplify array expressions.
/// \param src: an expression
/// \param array_symbol: a symbol expression representing an array
void remove_pointer_offsets(exprt &src, const symbol_exprt &array_symbol)
{
  if(src.id()==ID_pointer_offset &&
     src.op0().id()==ID_constant &&
     src.op0().op0().id()==ID_address_of &&
     src.op0().op0().op0().id()==ID_index)
  {
    const index_exprt &idx=to_index_expr(src.op0().op0().op0());
    const irep_idt &array_id=to_symbol_expr(idx.array()).get_identifier();
    if(idx.array().id()==ID_symbol &&
       array_id==array_symbol.get_identifier() &&
       to_constant_expr(idx.index()).value_is_zero_string())
      src=from_integer(0, src.type());
  }
  else
    for(auto &op : src.operands())
      remove_pointer_offsets(op, array_symbol);
}

/// Simplify the expression in index as much as possible to try to get an
/// unsigned constant.
/// \param idx: an expression representing an index in an array
/// \param out: a reference to an unsigned value of type size_t, which will hold
///   the result of the simplification if it is successful
/// \return Boolean flag that is true if the `idx` expression could not be
///   simplified into a unsigned constant value.
bool simplify_index(const exprt &idx, std::size_t &out)
{
  if(idx.id()==ID_constant)
  {
    std::string value_str(id2string(to_constant_expr(idx).get_value()));
    mp_integer int_value=binary2integer(value_str, false);
    if(int_value>std::numeric_limits<std::size_t>::max())
      return true;
    out=int_value.to_long();
    return false;
  }
  else if(idx.id()==ID_plus)
  {
    std::size_t l, r;
    if(!simplify_index(idx.op0(), l) && !simplify_index(idx.op1(), r))
    {
      out=l+r;
      return false;
    }
  }

  return true;
}

/// Simplify an expression before putting it in the json format
/// \param src: an expression potentialy containing array accesses (index_expr)
/// \return an expression similar in meaning to src but where array accesses
///   have been simplified
exprt simplify_array_access(const exprt &src)
{
  if(src.id()==ID_index && to_index_expr(src).array().id()==ID_symbol)
  {
    // Case where the array is a symbol.
    const symbol_exprt &array_symbol=to_symbol_expr(to_index_expr(src).array());
    exprt simplified_index=to_index_expr(src).index();
    // We remove potential appearances of `pointer_offset(array_symbol)`
    remove_pointer_offsets(simplified_index, array_symbol);
    return index_exprt(array_symbol, simplified_index);
  }
  else if(src.id()==ID_index && to_index_expr(src).array().id()==ID_array)
  {
    // Case where the array is given by an array of expressions
    exprt index=to_index_expr(src).index();
    remove_pointer_offsets(index);

    // We look for an actual integer value for the index
    std::size_t i;
    if(!simplify_index(index, i))
      return to_index_expr(src).array().operands()[i];
  }
  return src;
}

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

        assert(step.full_lhs.is_not_nil());
        exprt simplified=simplify_array_access(step.full_lhs);
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
          assert(step.full_lhs_value.is_not_nil());
          exprt simplified=simplify_array_access(step.full_lhs_value);
          full_lhs_value=json(simplified, ns, symbol->mode);
        }
        else
        {
          assert(step.full_lhs_value.is_not_nil());
          full_lhs_value=json(step.full_lhs_value, ns);
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
      break;

    case goto_trace_stept::typet::OUTPUT:
      {
        json_objectt &json_output=dest_array.push_back().make_object();

        json_output["stepType"]=json_stringt("output");
        json_output["hidden"]=jsont::json_boolean(step.hidden);
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
