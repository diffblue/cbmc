/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: July 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#include "goto_trace.h"

#include <cassert>
#include <ostream>

#include <util/arith_tools.h>
#include <util/config.h>
#include <util/symbol.h>

#include <ansi-c/printf_formatter.h>
#include <langapi/language_util.h>
#include "html_goto_trace.h"

void goto_tracet::output(
  const class namespacet &ns,
  std::ostream &out) const
{
  for(const auto &step : steps)
    step.output(ns, out);
}

void goto_trace_stept::output(
  const namespacet &ns,
  std::ostream &out) const
{
  out << "*** ";

  switch(type)
  {
  case goto_trace_stept::typet::ASSERT: out << "ASSERT"; break;
  case goto_trace_stept::typet::ASSUME: out << "ASSUME"; break;
  case goto_trace_stept::typet::LOCATION: out << "LOCATION"; break;
  case goto_trace_stept::typet::ASSIGNMENT: out << "ASSIGNMENT"; break;
  case goto_trace_stept::typet::GOTO: out << "GOTO"; break;
  case goto_trace_stept::typet::DECL: out << "DECL"; break;
  case goto_trace_stept::typet::DEAD: out << "DEAD"; break;
  case goto_trace_stept::typet::OUTPUT: out << "OUTPUT"; break;
  case goto_trace_stept::typet::INPUT: out << "INPUT"; break;
  case goto_trace_stept::typet::ATOMIC_BEGIN:
    out << "ATOMIC_BEGIN";
    break;
  case goto_trace_stept::typet::ATOMIC_END: out << "ATOMIC_END"; break;
  case goto_trace_stept::typet::SHARED_READ: out << "SHARED_READ"; break;
  case goto_trace_stept::typet::SHARED_WRITE: out << "SHARED WRITE"; break;
  case goto_trace_stept::typet::FUNCTION_CALL: out << "FUNCTION CALL"; break;
  case goto_trace_stept::typet::FUNCTION_RETURN:
    out << "FUNCTION RETURN"; break;
  default:
    out << "unknown type: " << static_cast<int>(type) << '\n';
    UNREACHABLE;
  }

  if(type==typet::ASSERT || type==typet::ASSUME || type==typet::GOTO)
    out << " (" << cond_value << ")";

  if(hidden)
    out << " hidden";

  out << '\n';

  if(!pc->source_location.is_nil())
    out << pc->source_location << '\n';

  if(pc->is_goto())
    out << "GOTO   ";
  else if(pc->is_assume())
    out << "ASSUME ";
  else if(pc->is_assert())
    out << "ASSERT ";
  else if(pc->is_dead())
    out << "DEAD   ";
  else if(pc->is_other())
    out << "OTHER  ";
  else if(pc->is_assign())
    out << "ASSIGN ";
  else if(pc->is_decl())
    out << "DECL   ";
  else if(pc->is_function_call())
    out << "CALL   ";
  else
    out << "(?)    ";

  out << '\n';

  if((pc->is_other() && lhs_object.is_not_nil()) || pc->is_assign())
  {
    irep_idt identifier=lhs_object.get_object_name();
    out << "  " << from_expr(ns, identifier, lhs_object.get_original_expr())
        << " = " << from_expr(ns, identifier, lhs_object_value)
        << '\n';
  }
  else if(pc->is_assert())
  {
    if(!cond_value)
    {
      out << "Violated property:" << '\n';
      if(pc->source_location.is_nil())
        out << "  " << pc->source_location << '\n';

      if(comment!="")
        out << "  " << comment << '\n';
      out << "  " << from_expr(ns, "", pc->guard) << '\n';
      out << '\n';
    }
  }

  out << '\n';
}

static std::string expr_to_hex(const exprt & expr)
{
  mp_integer value_int=binary2integer
      (id2string(to_constant_expr(expr).get_value()),
          false);
  return "0x" + integer2string(value_int, 16);
}

std::string trace_value_hex(
  const exprt &expr,
  const namespacet &ns)
{
  const typet &type=ns.follow(expr.type());

  if(expr.id()==ID_constant)
  {
    if(type.id()==ID_unsignedbv ||
       type.id()==ID_signedbv ||
       type.id()==ID_bv ||
       type.id()==ID_fixedbv ||
       type.id()==ID_floatbv ||
       type.id()==ID_pointer ||
       type.id()==ID_c_bit_field ||
       type.id()==ID_c_bool ||
       type.id()==ID_c_enum ||
       type.id()==ID_c_enum_tag)
    {
      return expr_to_hex(expr);
    }
    else if(type.id()==ID_bool)
    {
      return expr.is_true()?"1":"0";
    }
  }
  else if(expr.id()==ID_array)
  {
    std::string result;

    forall_operands(it, expr)
    {
      if(result=="")
        result="{ ";
      else
        result+=", ";
      result+=trace_value_hex(*it, ns);
    }

    return result+" }";
  }
  else if(expr.id()==ID_struct)
  {
    std::string result="{ ";

    forall_operands(it, expr)
    {
      if(it!=expr.operands().begin())
        result+=", ";
      result+=trace_value_hex(*it, ns);
    }

    return result+" }";
  }
  else if(expr.id()==ID_union)
  {
    assert(expr.operands().size()==1);
    return trace_value_hex(expr.op0(), ns);
  }

  return "?";
}


std::string trace_value_binary(
  const exprt &expr,
  const namespacet &ns)
{
  const typet &type=ns.follow(expr.type());

  if(expr.id()==ID_constant)
  {
    if(type.id()==ID_unsignedbv ||
       type.id()==ID_signedbv ||
       type.id()==ID_bv ||
       type.id()==ID_fixedbv ||
       type.id()==ID_floatbv ||
       type.id()==ID_pointer ||
       type.id()==ID_c_bit_field ||
       type.id()==ID_c_bool ||
       type.id()==ID_c_enum ||
       type.id()==ID_c_enum_tag)
    {
      return expr.get_string(ID_value);
    }
    else if(type.id()==ID_bool)
    {
      return expr.is_true()?"1":"0";
    }
  }
  else if(expr.id()==ID_array)
  {
    std::string result;

    forall_operands(it, expr)
    {
      if(result=="")
        result="{ ";
      else
        result+=", ";
      result+=trace_value_binary(*it, ns);
    }

    return result+" }";
  }
  else if(expr.id()==ID_struct)
  {
    std::string result="{ ";

    forall_operands(it, expr)
    {
      if(it!=expr.operands().begin())
        result+=", ";
      result+=trace_value_binary(*it, ns);
    }

    return result+" }";
  }
  else if(expr.id()==ID_union)
  {
    assert(expr.operands().size()==1);
    return trace_value_binary(expr.op0(), ns);
  }

  return "?";
}

static bool is_index_member_symbol(const exprt &src)
{
  if(src.id()==ID_index)
    return is_index_member_symbol(src.op0());
  else if(src.id()==ID_member)
    return is_index_member_symbol(src.op0());
  else if(src.id()==ID_symbol)
    return true;
  else
    return false;
}

void trace_value(
  std::ostream &out,
  const namespacet &ns,
  const goto_trace_stept &step)
{
  bool member_symbol = is_index_member_symbol(step.full_lhs);
  exprt value = member_symbol ? step.full_lhs_value : step.lhs_object_value;

  irep_idt identifier;

  if(step.lhs_object.is_not_nil())
    identifier=step.lhs_object.get_object_name();

  std::string value_string;


  if(value.is_nil())
    value_string="(assignment removed)";
  else
  {
    value_string=from_expr(ns, identifier, value);

    if(config.trace_config.numeric_representation ==
        configt::numeric_representationt::HEX)
      value_string += " (" + trace_value_hex(value, ns) + ")";
    else
      value_string += " (" + trace_value_binary(value, ns) + ")";
  }

  out << "  "
      << from_expr(ns, identifier,
          (member_symbol ? step.full_lhs : step.lhs_object))
      << "=" << value_string << '\n';
}


static void show_state_header(
  std::ostream &out,
  const namespacet &ns,
  const goto_trace_stept &state)
{
  out << '\n';

  if(state.step_nr==0)
    out << "Initial State";
  else
    out << "State " << state.step_nr;

  out << " " << state.pc->source_location
      << " thread " << state.thread_nr << '\n';
  out << "----------------------------------------------------" << '\n';

  if(config.trace_config.show_source_code)
    out << "Code:  " << as_string(ns, *state.pc) << '\n';
}

static void show_standard_goto_trace(
  std::ostream &out,
  const namespacet &ns,
  const goto_tracet &goto_trace)
{
  unsigned prev_step_nr=0;
  bool first_step=true;

  for(const auto &step : goto_trace.steps)
  {
    // hide the hidden ones
    if(step.hidden)
      continue;

    switch(step.type)
    {
    case goto_trace_stept::typet::ASSERT:
      if(!step.cond_value)
      {
        out << '\n';
        out << "Violated property:" << '\n';
        if(!step.pc->source_location.is_nil())
          out << "  " << step.pc->source_location << '\n';
        out << "  " << step.comment << '\n';

        if(step.pc->is_assert())
          out << "  " << from_expr(ns, "", step.pc->guard) << '\n';

        out << '\n';
      }
      break;

    case goto_trace_stept::typet::ASSUME:
      if(!step.cond_value)
      {
        out << '\n';
        out << "Assumption:" << '\n';
        if(!step.pc->source_location.is_nil())
          out << "  " << step.pc->source_location << '\n';

        if(step.pc->is_assume())
          out << "  " << from_expr(ns, "", step.pc->guard) << '\n';

        out << '\n';
      }
      break;

    case goto_trace_stept::typet::LOCATION:
      break;

    case goto_trace_stept::typet::GOTO:
      break;

    case goto_trace_stept::typet::ASSIGNMENT:
      if(config.trace_config.show_value_assignments)
      {
        if(step.pc->is_assign() || step.pc->is_return()
            || // returns have a lhs!
            step.pc->is_function_call()
            || (step.pc->is_other() && step.lhs_object.is_not_nil()))
        {
          if(prev_step_nr != step.step_nr || first_step)
          {
            first_step = false;
            prev_step_nr = step.step_nr;
            show_state_header(out, ns, step);
          }
          trace_value(out, ns, step);
        }
      }
      break;

    case goto_trace_stept::typet::DECL:
      if(config.trace_config.show_value_assignments)
      {
        if(prev_step_nr != step.step_nr || first_step)
        {
          first_step = false;
          prev_step_nr = step.step_nr;
          show_state_header(out, ns, step);
        }

        trace_value(out, ns, step);
      }
    break;

    case goto_trace_stept::typet::OUTPUT:
      if(config.trace_config.show_outputs)
      {
        if(step.formatted)
        {
          printf_formattert printf_formatter(ns);
          printf_formatter(id2string(step.format_string), step.io_args);
          printf_formatter.print(out);
          out << '\n';
        }
        else
        {
          show_state_header(out, ns, step);
          out << "  OUTPUT " << step.io_id << ":";

          bool first_output = true;
          for(const auto &arg : step.io_args)
          {
            if(!first_output)
              out << ";";
            out << " " << from_expr(ns, "", arg);

            if(config.trace_config.numeric_representation ==
                configt::numeric_representationt::HEX)
              out << " (" << trace_value_hex(arg, ns) << ")";
            else
              out << " (" << trace_value_binary(arg, ns) << ")";
            first_output = false;
          }

          out << '\n';
        }
      }
      break;

    case goto_trace_stept::typet::INPUT:
      if(config.trace_config.show_inputs)
      {
        show_state_header(out, ns, step);
        out << "  INPUT " << step.io_id << ":";

        bool first_input = true;
        for(const auto &arg : step.io_args)
        {
          if(!first_input)
            out << ";";
          out << " " << from_expr(ns, "", arg);

          if(config.trace_config.numeric_representation ==
              configt::numeric_representationt::HEX)
            out << " (" << trace_value_hex(arg, ns) << ")";
          else
            out << " (" << trace_value_binary(arg, ns) << ")";
          first_input = false;
        }

        out << '\n';
      }
      break;

    case goto_trace_stept::typet::FUNCTION_CALL:
      if(config.trace_config.show_function_calls)
        out << "Function call: " << as_string(ns, *step.pc) << '\n';
      break;
    case goto_trace_stept::typet::FUNCTION_RETURN:
      if(config.trace_config.show_function_calls)
        out << "Function return from: " << as_string(ns, *step.pc) << '\n';
      break;

    case goto_trace_stept::typet::SPAWN:
    case goto_trace_stept::typet::MEMORY_BARRIER:
    case goto_trace_stept::typet::ATOMIC_BEGIN:
    case goto_trace_stept::typet::ATOMIC_END:
    case goto_trace_stept::typet::DEAD:
      break;

    case goto_trace_stept::typet::CONSTRAINT:
    case goto_trace_stept::typet::SHARED_READ:
    case goto_trace_stept::typet::SHARED_WRITE:
    default:
      UNREACHABLE;
    }
  }
}

void show_goto_trace(
    std::ostream &out,
    const namespacet &ns,
    const goto_tracet &goto_trace)
{
  if(config.trace_config.trace_format == configt::trace_formatt::HTML)
    show_html_goto_trace(out, ns, goto_trace);
  else
    show_standard_goto_trace(out, ns, goto_trace);
}

