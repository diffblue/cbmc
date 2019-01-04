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
#include <util/range.h>
#include <util/string_utils.h>
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
  else if(is_function_call())
    out << ' ' << called_function;

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
/// \param ns: namespace for symbol type lookups
/// \param options: configuration options
/// \return a string with the numeric representation
static std::string numeric_representation(
  const constant_exprt &expr,
  const namespacet &ns,
  const trace_optionst &options)
{
  std::string result;
  std::string prefix;

  const typet &expr_type = expr.type();

  const typet &underlying_type =
    expr_type.id() == ID_c_enum_tag
      ? ns.follow_tag(to_c_enum_tag_type(expr_type)).subtype()
      : expr_type;

  const irep_idt &value = expr.get_value();

  const auto width = to_bitvector_type(underlying_type).get_width();

  const mp_integer value_int = bvrep2integer(id2string(value), width, false);

  if(options.hex_representation)
  {
    result = integer2string(value_int, 16);
    prefix = "0x";
  }
  else
  {
    result = integer2binary(value_int, width);
    prefix = "0b";
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
      return numeric_representation(to_constant_expr(expr), ns, options);
    }
    else if(type.id()==ID_bool)
    {
      return expr.is_true()?"1":"0";
    }
    else if(type.id()==ID_integer)
    {
      const auto i = numeric_cast<mp_integer>(expr);
      if(i.has_value() && *i >= 0)
      {
        if(options.hex_representation)
          return "0x" + integer2string(*i, 16);
        else
          return "0b" + integer2string(*i, 2);
      }
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

  out << from_expr(ns, identifier, full_lhs) << '=';

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

static std::string
state_location(const goto_trace_stept &state, const namespacet &ns)
{
  std::string result;

  const auto &source_location = state.pc->source_location;

  if(!source_location.get_file().empty())
    result += "file " + id2string(source_location.get_file());

  if(!state.function.empty())
  {
    const symbolt &symbol = ns.lookup(state.function);
    if(!result.empty())
      result += ' ';
    result += "function " + id2string(symbol.display_name());
  }

  if(!source_location.get_line().empty())
  {
    if(!result.empty())
      result += ' ';
    result += "line " + id2string(source_location.get_line());
  }

  if(!result.empty())
    result += ' ';
  result += "thread " + std::to_string(state.thread_nr);

  return result;
}

void show_state_header(
  messaget::mstreamt &out,
  const namespacet &ns,
  const goto_trace_stept &state,
  unsigned step_nr,
  const trace_optionst &options)
{
  out << '\n';

  if(step_nr == 0)
    out << "Initial State";
  else
    out << "State " << step_nr;

  out << ' ' << state_location(state, ns) << '\n';
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

/// \brief show a compact variant of the goto trace on the console
/// \param out: the output stream
/// \param ns: the namespace
/// \param goto_trace: the trace to be shown
/// \param options: any options, e.g., numerical representation
void show_compact_goto_trace(
  messaget::mstreamt &out,
  const namespacet &ns,
  const goto_tracet &goto_trace,
  const trace_optionst &options)
{
  std::size_t function_depth = 0;

  for(const auto &step : goto_trace.steps)
  {
    if(step.is_function_call())
      function_depth++;
    else if(step.is_function_return())
      function_depth--;

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
          out << "  " << state_location(step, ns) << '\n';

        out << "  " << messaget::red << step.comment << messaget::reset << '\n';

        if(step.pc->is_assert())
          out << "  " << from_expr(ns, step.function, step.pc->guard) << '\n';

        out << '\n';
      }
      break;

    case goto_trace_stept::typet::ASSIGNMENT:
      if(
        step.assignment_type ==
        goto_trace_stept::assignment_typet::ACTUAL_PARAMETER)
      {
        break;
      }

      out << "  ";

      if(!step.pc->source_location.get_line().empty())
      {
        out << messaget::faint << step.pc->source_location.get_line() << ':'
            << messaget::reset << ' ';
      }

      trace_value(
        out,
        ns,
        step.get_lhs_object(),
        step.full_lhs,
        step.full_lhs_value,
        options);
      break;

    case goto_trace_stept::typet::FUNCTION_CALL:
      // downwards arrow
      out << '\n' << messaget::faint << u8"\u21b3" << messaget::reset << ' ';
      if(!step.pc->source_location.get_file().empty())
      {
        out << messaget::faint << step.pc->source_location.get_file();

        if(!step.pc->source_location.get_line().empty())
        {
          out << messaget::faint << ':' << step.pc->source_location.get_line();
        }

        out << messaget::reset << ' ';
      }

      {
        // show the display name
        const auto &f_symbol = ns.lookup(step.called_function);
        out << f_symbol.display_name();
      }

      {
        auto arg_strings = make_range(step.function_arguments)
                             .map([&ns, &step](const exprt &arg) {
                               return from_expr(ns, step.function, arg);
                             });

        out << '(';
        join_strings(out, arg_strings.begin(), arg_strings.end(), ", ");
        out << ")\n";
      }

      break;

    case goto_trace_stept::typet::FUNCTION_RETURN:
      // upwards arrow
      out << messaget::faint << u8"\u21b5" << messaget::reset << '\n';
      break;

    case goto_trace_stept::typet::ASSUME:
    case goto_trace_stept::typet::LOCATION:
    case goto_trace_stept::typet::GOTO:
    case goto_trace_stept::typet::DECL:
    case goto_trace_stept::typet::OUTPUT:
    case goto_trace_stept::typet::INPUT:
    case goto_trace_stept::typet::SPAWN:
    case goto_trace_stept::typet::MEMORY_BARRIER:
    case goto_trace_stept::typet::ATOMIC_BEGIN:
    case goto_trace_stept::typet::ATOMIC_END:
    case goto_trace_stept::typet::DEAD:
      break;

    default:
      UNREACHABLE;
    }
  }
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
        {
          out << "  " << state_location(step, ns) << '\n';
        }

        out << "  " << messaget::red << step.comment << messaget::reset << '\n';

        if(step.pc->is_assert())
          out << "  " << from_expr(ns, step.function, step.pc->guard) << '\n';

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
          out << "  " << from_expr(ns, step.function, step.pc->guard) << '\n';

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
          show_state_header(out, ns, step, step.step_nr, options);
        }

        out << "  ";
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
        show_state_header(out, ns, step, step.step_nr, options);
      }

      out << "  ";
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
        show_state_header(out, ns, step, step.step_nr, options);
        out << "  OUTPUT " << step.io_id << ':';

        for(std::list<exprt>::const_iterator
            l_it=step.io_args.begin();
            l_it!=step.io_args.end();
            l_it++)
        {
          if(l_it!=step.io_args.begin())
            out << ';';

          out << ' ' << from_expr(ns, step.function, *l_it);

          // the binary representation
          out << " (" << trace_numeric_value(*l_it, ns, options) << ')';
        }

        out << '\n';
      }
      break;

    case goto_trace_stept::typet::INPUT:
      show_state_header(out, ns, step, step.step_nr, options);
      out << "  INPUT " << step.io_id << ':';

      for(std::list<exprt>::const_iterator
          l_it=step.io_args.begin();
          l_it!=step.io_args.end();
          l_it++)
      {
        if(l_it!=step.io_args.begin())
          out << ';';

        out << ' ' << from_expr(ns, step.function, *l_it);

        // the binary representation
        out << " (" << trace_numeric_value(*l_it, ns, options) << ')';
      }

      out << '\n';
      break;

    case goto_trace_stept::typet::FUNCTION_CALL:
      function_depth++;
      if(options.show_function_calls)
      {
        out << "\n#### Function call: " << step.called_function;
        out << '(';

        bool first = true;
        for(auto &arg : step.function_arguments)
        {
          if(first)
            first = false;
          else
            out << ", ";

          out << from_expr(ns, step.function, arg);
        }

        out << ") (depth " << function_depth << ") ####\n";
      }
      break;

    case goto_trace_stept::typet::FUNCTION_RETURN:
      function_depth--;
      if(options.show_function_calls)
      {
        out << "\n#### Function return from " << step.function << " (depth "
            << function_depth << ") ####\n";
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

static void show_goto_stack_trace(
  messaget::mstreamt &out,
  const namespacet &ns,
  const goto_tracet &goto_trace)
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
      out << "  " << step.called_function;
      out << '(';

      bool first = true;
      for(auto &arg : step.function_arguments)
      {
        if(first)
          first = false;
        else
          out << ", ";

        out << from_expr(ns, step.function, arg);
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
    show_goto_stack_trace(out, ns, goto_trace);
  else if(options.compact_trace)
    show_compact_goto_trace(out, ns, goto_trace, options);
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
