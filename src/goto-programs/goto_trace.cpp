/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: July 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#include "goto_trace.h"

#include <ostream>

#include <util/arith_tools.h>
#include <util/format_expr.h>
#include <util/symbol.h>

#include <langapi/language_util.h>

#include "printf_formatter.h"

static optionalt<symbol_exprt> get_object_rec(const exprt &src)
{
  if(src.id()==ID_symbol)
    return to_symbol_expr(src);
  else if(src.id()==ID_member)
    return get_object_rec(to_member_expr(src).struct_op());
  else if(src.id()==ID_index)
    return get_object_rec(to_index_expr(src).array());
  else if(src.id()==ID_typecast)
    return get_object_rec(to_typecast_expr(src).op());
  else
    return {}; // give up
}

optionalt<symbol_exprt> goto_trace_stept::get_lhs_object() const
{
  return get_object_rec(full_lhs);
}

void goto_tracet::output(
  const class namespacet &ns,
  std::ostream &out) const
{
  for(const auto &step : steps)
    step.output(ns, out);
}

void goto_trace_stept::output(
  const namespacet &,
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

  if(is_assert() || is_assume() || is_goto())
    out << " (" << cond_value << ')';
  else if(is_function_call() || is_function_return())
    out << ' ' << function_identifier;

  if(hidden)
    out << " hidden";

  out << '\n';

  if(is_assignment())
  {
    out << "  " << format(full_lhs)
        << " = " << format(full_lhs_value)
        << '\n';
  }

  if(!pc->source_location.is_nil())
    out << pc->source_location << '\n';

  out << pc->type << '\n';

  if(pc->is_assert())
  {
    if(!cond_value)
    {
      out << "Violated property:" << '\n';
      if(pc->source_location.is_nil())
        out << "  " << pc->source_location << '\n';

      if(!comment.empty())
        out << "  " << comment << '\n';

      out << "  " << format(pc->guard) << '\n';
      out << '\n';
    }
  }

  out << '\n';
}
/// Returns the numeric representation of an expression, based on
/// options. The default is binary without a base-prefix. Setting
/// options.hex_representation to be true outputs hex format. Setting
/// options.base_prefix to be true appends either 0b or 0x to the number
/// to indicate the base
/// \param expr: expression to get numeric representation from
/// \param options: configuration options
/// \return a string with the numeric representation
static std::string
numeric_representation(const exprt &expr, const trace_optionst &options)
{
  std::string result;
  std::string prefix;
  if(options.hex_representation)
  {
    mp_integer value_int =
      bv2integer(id2string(to_constant_expr(expr).get_value()), false);
    result = integer2string(value_int, 16);
    prefix = "0x";
  }
  else
  {
    prefix = "0b";
    result = expr.get_string(ID_value);
  }

  std::ostringstream oss;
  std::string::size_type i = 0;
  for(const auto c : result)
  {
    oss << c;
    if(++i % 8 == 0 && result.size() != i)
      oss << ' ';
  }
  if(options.base_prefix)
    return prefix + oss.str();
  else
    return oss.str();
}

std::string trace_numeric_value(
  const exprt &expr,
  const namespacet &ns,
  const trace_optionst &options)
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
      const std::string &str = numeric_representation(expr, options);
      return str;
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
      result+=trace_numeric_value(*it, ns, options);
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
      result+=trace_numeric_value(*it, ns, options);
    }

    return result+" }";
  }
  else if(expr.id()==ID_union)
  {
    PRECONDITION(expr.operands().size()==1);
    return trace_numeric_value(expr.op0(), ns, options);
  }

  return "?";
}

void trace_value(
  messaget::mstreamt &out,
  const namespacet &ns,
  const optionalt<symbol_exprt> &lhs_object,
  const exprt &full_lhs,
  const exprt &value,
  const trace_optionst &options)
{
  irep_idt identifier;

  if(lhs_object.has_value())
    identifier=lhs_object->get_identifier();

  out << "  " << from_expr(ns, identifier, full_lhs) << '=';

  if(value.is_nil())
    out << "(assignment removed)";
  else
  {
    out << from_expr(ns, identifier, value);

    // the binary representation
    out << ' ' << messaget::faint << '('
        << trace_numeric_value(value, ns, options) << ')' << messaget::reset;
  }

  out << '\n';
}

void show_state_header(
  messaget::mstreamt &out,
  const namespacet &ns,
  const goto_trace_stept &state,
  const source_locationt &source_location,
  unsigned step_nr,
  const trace_optionst &options)
{
  out << '\n';

  if(step_nr == 0)
    out << "Initial State";
  else
    out << "State " << step_nr;

  out << ' ' << source_location << " thread " << state.thread_nr << '\n';
  out << "----------------------------------------------------" << '\n';

  if(options.show_code)
  {
    out << as_string(ns, *state.pc) << '\n';
    out << "----------------------------------------------------" << '\n';
  }
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

void show_full_goto_trace(
  messaget::mstreamt &out,
  const namespacet &ns,
  const goto_tracet &goto_trace,
  const trace_optionst &options)
{
  unsigned prev_step_nr=0;
  bool first_step=true;
  std::size_t function_depth=0;

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
        out << messaget::red << "Violated property:" << messaget::reset << '\n';
        if(!step.pc->source_location.is_nil())
          out << "  " << step.pc->source_location << '\n';
        out << "  " << messaget::red << step.comment << messaget::reset << '\n';

        if(step.pc->is_assert())
          out << "  " << from_expr(ns, step.pc->function, step.pc->guard)
              << '\n';

        out << '\n';
      }
      break;

    case goto_trace_stept::typet::ASSUME:
      if(!step.cond_value)
      {
        out << '\n';
        out << "Violated assumption:" << '\n';
        if(!step.pc->source_location.is_nil())
          out << "  " << step.pc->source_location << '\n';

        if(step.pc->is_assume())
          out << "  " << from_expr(ns, step.pc->function, step.pc->guard)
              << '\n';

        out << '\n';
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
         (step.pc->is_other() && step.full_lhs.is_not_nil()))
      {
        if(prev_step_nr!=step.step_nr || first_step)
        {
          first_step=false;
          prev_step_nr=step.step_nr;
          show_state_header(
            out, ns, step, step.pc->source_location, step.step_nr, options);
        }

       trace_value(
         out,
         ns,
         step.get_lhs_object(),
         step.full_lhs,
         step.full_lhs_value,
         options);
      }
      break;

    case goto_trace_stept::typet::DECL:
      if(prev_step_nr!=step.step_nr || first_step)
      {
        first_step=false;
        prev_step_nr=step.step_nr;
        show_state_header(
          out, ns, step, step.pc->source_location, step.step_nr, options);
      }

      trace_value(
        out, ns, step.get_lhs_object(), step.full_lhs, step.full_lhs_value, options);
      break;

    case goto_trace_stept::typet::OUTPUT:
      if(step.formatted)
      {
        printf_formattert printf_formatter(ns);
        printf_formatter(id2string(step.format_string), step.io_args);
        printf_formatter.print(out);
        out << '\n';
      }
      else
      {
        show_state_header(
          out, ns, step, step.pc->source_location, step.step_nr, options);
        out << "  OUTPUT " << step.io_id << ':';

        for(std::list<exprt>::const_iterator
            l_it=step.io_args.begin();
            l_it!=step.io_args.end();
            l_it++)
        {
          if(l_it!=step.io_args.begin())
            out << ';';
          out << ' ' << from_expr(ns, step.pc->function, *l_it);

          // the binary representation
          out << " (" << trace_numeric_value(*l_it, ns, options) << ')';
        }

        out << '\n';
      }
      break;

    case goto_trace_stept::typet::INPUT:
      show_state_header(
        out, ns, step, step.pc->source_location, step.step_nr, options);
      out << "  INPUT " << step.io_id << ':';

      for(std::list<exprt>::const_iterator
          l_it=step.io_args.begin();
          l_it!=step.io_args.end();
          l_it++)
      {
        if(l_it!=step.io_args.begin())
          out << ';';
        out << ' ' << from_expr(ns, step.pc->function, *l_it);

        // the binary representation
        out << " (" << trace_numeric_value(*l_it, ns, options) << ')';
      }

      out << '\n';
      break;

    case goto_trace_stept::typet::FUNCTION_CALL:
      function_depth++;
      if(options.show_function_calls)
      {
        out << "\n#### Function call: " << step.function_identifier;
        out << '(';

        bool first = true;
        for(auto &arg : step.function_arguments)
        {
          if(first)
            first = false;
          else
            out << ", ";

          out << from_expr(ns, step.function_identifier, arg);
        }

        out << ") (depth " << function_depth << ") ####\n";
      }
      break;

    case goto_trace_stept::typet::FUNCTION_RETURN:
      function_depth--;
      if(options.show_function_calls)
      {
        out << "\n#### Function return: " << step.function_identifier
            << " (depth " << function_depth << ") ####\n";
      }
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

void show_goto_stack_trace(
  messaget::mstreamt &out,
  const namespacet &ns,
  const goto_tracet &goto_trace,
  const trace_optionst &options)
{
  // map from thread number to a call stack
  std::map<unsigned, std::vector<goto_tracet::stepst::const_iterator>>
    call_stacks;

  // by default, we show thread 0
  unsigned thread_to_show = 0;

  for(auto s_it = goto_trace.steps.begin(); s_it != goto_trace.steps.end();
      s_it++)
  {
    const auto &step = *s_it;
    auto &stack = call_stacks[step.thread_nr];

    if(step.is_assert())
    {
      if(!step.cond_value)
      {
        stack.push_back(s_it);
        thread_to_show = step.thread_nr;
      }
    }
    else if(step.is_function_call())
    {
      stack.push_back(s_it);
    }
    else if(step.is_function_return())
    {
      stack.pop_back();
    }
  }

  const auto &stack = call_stacks[thread_to_show];

  // print in reverse order
  for(auto s_it = stack.rbegin(); s_it != stack.rend(); s_it++)
  {
    const auto &step = **s_it;
    if(step.is_assert())
    {
      out << "  assertion failure";
      if(!step.pc->source_location.is_nil())
        out << ' ' << step.pc->source_location;
      out << '\n';
    }
    else if(step.is_function_call())
    {
      out << "  " << step.function_identifier;
      out << '(';

      bool first = true;
      for(auto &arg : step.function_arguments)
      {
        if(first)
          first = false;
        else
          out << ", ";

        out << from_expr(ns, step.function_identifier, arg);
      }

      out << ')';

      if(!step.pc->source_location.is_nil())
        out << ' ' << step.pc->source_location;

      out << '\n';
    }
  }
}

void show_goto_trace(
  messaget::mstreamt &out,
  const namespacet &ns,
  const goto_tracet &goto_trace,
  const trace_optionst &options)
{
  if(options.stack_trace)
    show_goto_stack_trace(out, ns, goto_trace, options);
  else
    show_full_goto_trace(out, ns, goto_trace, options);
}

void show_goto_trace(
  messaget::mstreamt &out,
  const namespacet &ns,
  const goto_tracet &goto_trace)
{
  show_goto_trace(out, ns, goto_trace, trace_optionst::default_options);
}

const trace_optionst trace_optionst::default_options = trace_optionst();
