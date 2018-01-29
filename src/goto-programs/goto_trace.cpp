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
#include <util/symbol.h>

#include <ansi-c/printf_formatter.h>
#include <langapi/language_util.h>

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
    out << "unknown type: " << static_cast<int>(type) << std::endl;
    UNREACHABLE;
  }

  if(type==typet::ASSERT || type==typet::ASSUME || type==typet::GOTO)
    out << " (" << cond_value << ")";

  if(hidden)
    out << " hidden";

  out << "\n";

  if(!pc->source_location.is_nil())
    out << pc->source_location << "\n";

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

  out << "\n";

  if((pc->is_other() && lhs_object.is_not_nil()) || pc->is_assign())
  {
    irep_idt identifier=lhs_object.get_object_name();
    out << "  " << from_expr(ns, identifier, lhs_object.get_original_expr())
        << " = " << from_expr(ns, identifier, lhs_object_value)
        << "\n";
  }
  else if(pc->is_assert())
  {
    if(!cond_value)
    {
      out << "Violated property:" << "\n";
      if(pc->source_location.is_nil())
        out << "  " << pc->source_location << "\n";

      if(comment!="")
        out << "  " << comment << "\n";
      out << "  " << from_expr(ns, "", pc->guard) << "\n";
      out << "\n";
    }
  }

  out << "\n";
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
    else if(type.id()==ID_integer)
    {
      mp_integer i;
      if(!to_integer(expr, i) && i>=0)
        return integer2string(i, 2);
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

void trace_value(
  std::ostream &out,
  const namespacet &ns,
  const ssa_exprt &lhs_object,
  const exprt &full_lhs,
  const exprt &value)
{
  irep_idt identifier;

  if(lhs_object.is_not_nil())
    identifier=lhs_object.get_object_name();

  std::string value_string;

  if(value.is_nil())
    value_string="(assignment removed)";
  else
  {
    value_string=from_expr(ns, identifier, value);

    // the binary representation
    value_string+=" ("+trace_value_binary(value, ns)+")";
  }

  out << "  "
      << from_expr(ns, identifier, full_lhs)
      << "=" << value_string
      << "\n";
}

void show_state_header(
  std::ostream &out,
  const goto_trace_stept &state,
  const source_locationt &source_location,
  unsigned step_nr)
{
  out << "\n";

  if(step_nr==0)
    out << "Initial State";
  else
    out << "State " << step_nr;

  out << " " << source_location
      << " thread " << state.thread_nr << "\n";
  out << "----------------------------------------------------" << "\n";
}

bool is_index_member_symbol(const exprt &src)
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

void show_goto_trace(
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
        out << "\n";
        out << "Violated property:" << "\n";
        if(!step.pc->source_location.is_nil())
          out << "  " << step.pc->source_location << "\n";
        out << "  " << step.comment << "\n";

        if(step.pc->is_assert())
          out << "  " << from_expr(ns, "", step.pc->guard) << "\n";

        out << "\n";
      }
      break;

    case goto_trace_stept::typet::ASSUME:
      if(!step.cond_value)
      {
        out << "\n";
        out << "Violated assumption:" << "\n";
        if(!step.pc->source_location.is_nil())
          out << "  " << step.pc->source_location << "\n";

        if(step.pc->is_assume())
          out << "  " << from_expr(ns, "", step.pc->guard) << "\n";

        out << "\n";
      }
      break;

    case goto_trace_stept::typet::LOCATION:
      break;

    case goto_trace_stept::typet::GOTO:
      break;

    case goto_trace_stept::typet::ASSIGNMENT:
      if(step.pc->is_assign() ||
         step.pc->is_return() || // returns have a lhs!
         step.pc->is_function_call() ||
         (step.pc->is_other() && step.lhs_object.is_not_nil()))
      {
        if(prev_step_nr!=step.step_nr || first_step)
        {
          first_step=false;
          prev_step_nr=step.step_nr;
          show_state_header(out, step, step.pc->source_location, step.step_nr);
        }

        // see if the full lhs is something clean
        if(is_index_member_symbol(step.full_lhs))
          trace_value(
            out, ns, step.lhs_object, step.full_lhs, step.full_lhs_value);
        else
          trace_value(
            out, ns, step.lhs_object, step.lhs_object, step.lhs_object_value);
      }
      break;

    case goto_trace_stept::typet::DECL:
      if(prev_step_nr!=step.step_nr || first_step)
      {
        first_step=false;
        prev_step_nr=step.step_nr;
        show_state_header(out, step, step.pc->source_location, step.step_nr);
      }

      trace_value(out, ns, step.lhs_object, step.full_lhs, step.full_lhs_value);
      break;

    case goto_trace_stept::typet::OUTPUT:
      if(step.formatted)
      {
        printf_formattert printf_formatter(ns);
        printf_formatter(id2string(step.format_string), step.io_args);
        printf_formatter.print(out);
        out << "\n";
      }
      else
      {
        show_state_header(out, step, step.pc->source_location, step.step_nr);
        out << "  OUTPUT " << step.io_id << ":";

        for(std::list<exprt>::const_iterator
            l_it=step.io_args.begin();
            l_it!=step.io_args.end();
            l_it++)
        {
          if(l_it!=step.io_args.begin())
            out << ";";
          out << " " << from_expr(ns, "", *l_it);

          // the binary representation
          out << " (" << trace_value_binary(*l_it, ns) << ")";
        }

        out << "\n";
      }
      break;

    case goto_trace_stept::typet::INPUT:
      show_state_header(out, step, step.pc->source_location, step.step_nr);
      out << "  INPUT " << step.io_id << ":";

      for(std::list<exprt>::const_iterator
          l_it=step.io_args.begin();
          l_it!=step.io_args.end();
          l_it++)
      {
        if(l_it!=step.io_args.begin())
          out << ";";
        out << " " << from_expr(ns, "", *l_it);

        // the binary representation
        out << " (" << trace_value_binary(*l_it, ns) << ")";
      }

      out << "\n";
      break;

    case goto_trace_stept::typet::FUNCTION_CALL:
    case goto_trace_stept::typet::FUNCTION_RETURN:
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


const trace_optionst trace_optionst::default_options = trace_optionst();
