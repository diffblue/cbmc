/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution
/// Implementation of functions to build SSA equation.

#include "symex_target_equation.h"

#include <util/format_expr.h>
#include <util/std_expr.h>
#include <util/throw_with_nested.h>
#include <util/unwrap_nested_exception.h>

// Can be removed once deprecated SSA_stept::output is removed
#include <langapi/language_util.h>

#include <solvers/flattening/bv_conversion_exceptions.h>
#include <solvers/prop/literal_expr.h>
#include <solvers/prop/prop.h>
#include <solvers/prop/prop_conv.h>

#include "equation_conversion_exceptions.h"
#include "goto_symex_state.h"

void symex_target_equationt::shared_read(
  const exprt &guard,
  const ssa_exprt &ssa_object,
  unsigned atomic_section_id,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::SHARED_READ);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.ssa_lhs=ssa_object;
  SSA_step.atomic_section_id=atomic_section_id;

  merge_ireps(SSA_step);
}

void symex_target_equationt::shared_write(
  const exprt &guard,
  const ssa_exprt &ssa_object,
  unsigned atomic_section_id,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::SHARED_WRITE);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.ssa_lhs=ssa_object;
  SSA_step.atomic_section_id=atomic_section_id;

  merge_ireps(SSA_step);
}

/// spawn a new thread
void symex_target_equationt::spawn(
  const exprt &guard,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::SPAWN);
  SSA_stept &SSA_step=SSA_steps.back();
  SSA_step.guard=guard;

  merge_ireps(SSA_step);
}

void symex_target_equationt::memory_barrier(
  const exprt &guard,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::MEMORY_BARRIER);
  SSA_stept &SSA_step=SSA_steps.back();
  SSA_step.guard=guard;

  merge_ireps(SSA_step);
}

/// start an atomic section
void symex_target_equationt::atomic_begin(
  const exprt &guard,
  unsigned atomic_section_id,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::ATOMIC_BEGIN);
  SSA_stept &SSA_step=SSA_steps.back();
  SSA_step.guard=guard;
  SSA_step.atomic_section_id=atomic_section_id;

  merge_ireps(SSA_step);
}

/// end an atomic section
void symex_target_equationt::atomic_end(
  const exprt &guard,
  unsigned atomic_section_id,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::ATOMIC_END);
  SSA_stept &SSA_step=SSA_steps.back();
  SSA_step.guard=guard;
  SSA_step.atomic_section_id=atomic_section_id;

  merge_ireps(SSA_step);
}

void symex_target_equationt::assignment(
  const exprt &guard,
  const ssa_exprt &ssa_lhs,
  const exprt &ssa_full_lhs,
  const exprt &original_full_lhs,
  const exprt &ssa_rhs,
  const sourcet &source,
  assignment_typet assignment_type)
{
  PRECONDITION(ssa_lhs.is_not_nil());

  SSA_steps.emplace_back(source, goto_trace_stept::typet::ASSIGNMENT);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.ssa_lhs=ssa_lhs;
  SSA_step.ssa_full_lhs=ssa_full_lhs;
  SSA_step.original_full_lhs=original_full_lhs;
  SSA_step.ssa_rhs=ssa_rhs;
  SSA_step.assignment_type=assignment_type;

  SSA_step.cond_expr=equal_exprt(SSA_step.ssa_lhs, SSA_step.ssa_rhs);
  SSA_step.hidden=(assignment_type!=assignment_typet::STATE &&
                   assignment_type!=assignment_typet::VISIBLE_ACTUAL_PARAMETER);

  merge_ireps(SSA_step);
}

void symex_target_equationt::decl(
  const exprt &guard,
  const ssa_exprt &ssa_lhs,
  const sourcet &source,
  assignment_typet assignment_type)
{
  PRECONDITION(ssa_lhs.is_not_nil());

  SSA_steps.emplace_back(source, goto_trace_stept::typet::DECL);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.ssa_lhs=ssa_lhs;
  SSA_step.ssa_full_lhs=ssa_lhs;
  SSA_step.original_full_lhs=ssa_lhs.get_original_expr();
  SSA_step.hidden=(assignment_type!=assignment_typet::STATE);

  // the condition is trivially true, and only
  // there so we see the symbols
  SSA_step.cond_expr=equal_exprt(SSA_step.ssa_lhs, SSA_step.ssa_lhs);

  merge_ireps(SSA_step);
}

/// declare a fresh variable
void symex_target_equationt::dead(
  const exprt &,
  const ssa_exprt &,
  const sourcet &)
{
  // we currently don't record these
}

void symex_target_equationt::location(
  const exprt &guard,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::LOCATION);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;

  merge_ireps(SSA_step);
}

void symex_target_equationt::function_call(
  const exprt &guard,
  const irep_idt &function_identifier,
  const std::vector<exprt> &ssa_function_arguments,
  const sourcet &source,
  const bool hidden)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::FUNCTION_CALL);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard = guard;
  SSA_step.called_function = function_identifier;
  SSA_step.ssa_function_arguments = ssa_function_arguments;
  SSA_step.hidden = hidden;

  merge_ireps(SSA_step);
}

void symex_target_equationt::function_return(
  const exprt &guard,
  const sourcet &source,
  const bool hidden)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::FUNCTION_RETURN);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard = guard;
  SSA_step.hidden = hidden;

  merge_ireps(SSA_step);
}

void symex_target_equationt::output(
  const exprt &guard,
  const sourcet &source,
  const irep_idt &output_id,
  const std::list<exprt> &args)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::OUTPUT);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.io_args=args;
  SSA_step.io_id=output_id;

  merge_ireps(SSA_step);
}

void symex_target_equationt::output_fmt(
  const exprt &guard,
  const sourcet &source,
  const irep_idt &output_id,
  const irep_idt &fmt,
  const std::list<exprt> &args)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::OUTPUT);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.io_args=args;
  SSA_step.io_id=output_id;
  SSA_step.formatted=true;
  SSA_step.format_string=fmt;

  merge_ireps(SSA_step);
}

void symex_target_equationt::input(
  const exprt &guard,
  const sourcet &source,
  const irep_idt &input_id,
  const std::list<exprt> &args)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::INPUT);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.io_args=args;
  SSA_step.io_id=input_id;

  merge_ireps(SSA_step);
}

void symex_target_equationt::assumption(
  const exprt &guard,
  const exprt &cond,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::ASSUME);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.cond_expr=cond;

  merge_ireps(SSA_step);
}

void symex_target_equationt::assertion(
  const exprt &guard,
  const exprt &cond,
  const std::string &msg,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::ASSERT);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.cond_expr=cond;
  SSA_step.comment=msg;

  merge_ireps(SSA_step);
}

void symex_target_equationt::goto_instruction(
  const exprt &guard,
  const exprt &cond,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::GOTO);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.cond_expr=cond;

  merge_ireps(SSA_step);
}

void symex_target_equationt::constraint(
  const exprt &cond,
  const std::string &msg,
  const sourcet &source)
{
  // like assumption, but with global effect
  SSA_steps.emplace_back(source, goto_trace_stept::typet::CONSTRAINT);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=true_exprt();
  SSA_step.cond_expr=cond;
  SSA_step.comment=msg;

  merge_ireps(SSA_step);
}

void symex_target_equationt::convert(
  prop_convt &prop_conv)
{
  try
  {
    convert_guards(prop_conv);
    convert_assignments(prop_conv);
    convert_decls(prop_conv);
    convert_assumptions(prop_conv);
    convert_assertions(prop_conv);
    convert_goto_instructions(prop_conv);
    convert_function_calls(prop_conv);
    convert_io(prop_conv);
    convert_constraints(prop_conv);
  }
  catch(const equation_conversion_exceptiont &conversion_exception)
  {
    // unwrap the except and throw like normal
    const std::string full_error = unwrap_exception(conversion_exception);
    throw full_error;
  }
}

void symex_target_equationt::convert_assignments(
  decision_proceduret &decision_procedure) const
{
  for(const auto &step : SSA_steps)
  {
    if(step.is_assignment() && !step.ignore)
    {
      decision_procedure.conditional_output(
        decision_procedure.debug(),
        [&step](messaget::mstreamt &mstream) {
          step.output(mstream);
          mstream << messaget::eom;
        });

      decision_procedure.set_to_true(step.cond_expr);
    }
  }
}

void symex_target_equationt::convert_decls(
  prop_convt &prop_conv) const
{
  for(const auto &step : SSA_steps)
  {
    if(step.is_decl() && !step.ignore)
    {
      // The result is not used, these have no impact on
      // the satisfiability of the formula.
      try
      {
        prop_conv.convert(step.cond_expr);
      }
      catch(const bitvector_conversion_exceptiont &)
      {
        util_throw_with_nested(
          equation_conversion_exceptiont(
            "Error converting decls for step", step));
      }
    }
  }
}

void symex_target_equationt::convert_guards(
  prop_convt &prop_conv)
{
  for(auto &step : SSA_steps)
  {
    if(step.ignore)
      step.guard_literal=const_literal(false);
    else
    {
      prop_conv.conditional_output(
        prop_conv.debug(),
        [&step](messaget::mstreamt &mstream) {
          step.output(mstream);
          mstream << messaget::eom;
        });

      try
      {
        step.guard_literal = prop_conv.convert(step.guard);
      }
      catch(const bitvector_conversion_exceptiont &)
      {
        util_throw_with_nested(
          equation_conversion_exceptiont(
            "Error converting guard for step", step));
      }
    }
  }
}

void symex_target_equationt::convert_assumptions(
  prop_convt &prop_conv)
{
  for(auto &step : SSA_steps)
  {
    if(step.is_assume())
    {
      if(step.ignore)
        step.cond_literal=const_literal(true);
      else
      {
        prop_conv.conditional_output(
          prop_conv.debug(),
          [&step](messaget::mstreamt &mstream) {
            step.output(mstream);
            mstream << messaget::eom;
          });

        try
        {
          step.cond_literal = prop_conv.convert(step.cond_expr);
        }
        catch(const bitvector_conversion_exceptiont &)
        {
          util_throw_with_nested(
            equation_conversion_exceptiont(
              "Error converting assumptions for step", step));
        }
      }
    }
  }
}

void symex_target_equationt::convert_goto_instructions(
  prop_convt &prop_conv)
{
  for(auto &step : SSA_steps)
  {
    if(step.is_goto())
    {
      if(step.ignore)
        step.cond_literal=const_literal(true);
      else
      {
        prop_conv.conditional_output(
          prop_conv.debug(),
          [&step](messaget::mstreamt &mstream) {
            step.output(mstream);
            mstream << messaget::eom;
          });

        try
        {
          step.cond_literal = prop_conv.convert(step.cond_expr);
        }
        catch(const bitvector_conversion_exceptiont &)
        {
          util_throw_with_nested(
            equation_conversion_exceptiont(
              "Error converting goto instructions for step", step));
        }
      }
    }
  }
}

void symex_target_equationt::convert_constraints(
  decision_proceduret &decision_procedure) const
{
  for(const auto &step : SSA_steps)
  {
    if(step.is_constraint())
    {
      if(!step.ignore)
      {
        decision_procedure.conditional_output(
          decision_procedure.debug(),
          [&step](messaget::mstreamt &mstream) {
            step.output(mstream);
            mstream << messaget::eom;
          });

        try
        {
          decision_procedure.set_to_true(step.cond_expr);
        }
        catch(const bitvector_conversion_exceptiont &)
        {
          util_throw_with_nested(
            equation_conversion_exceptiont(
              "Error converting constraints for step", step));
        }
      }
    }
  }
}

void symex_target_equationt::convert_assertions(
  prop_convt &prop_conv)
{
  // we find out if there is only _one_ assertion,
  // which allows for a simpler formula

  std::size_t number_of_assertions=count_assertions();

  if(number_of_assertions==0)
    return;

  if(number_of_assertions==1)
  {
    for(auto &step : SSA_steps)
    {
      if(step.is_assert())
      {
        prop_conv.set_to_false(step.cond_expr);
        step.cond_literal=const_literal(false);
        return; // prevent further assumptions!
      }
      else if(step.is_assume())
        prop_conv.set_to_true(step.cond_expr);
    }

    UNREACHABLE; // unreachable
  }

  // We do (NOT a1) OR (NOT a2) ...
  // where the a's are the assertions
  or_exprt::operandst disjuncts;
  disjuncts.reserve(number_of_assertions);

  exprt assumption=true_exprt();

  for(auto &step : SSA_steps)
  {
    if(step.is_assert())
    {
      prop_conv.conditional_output(
        prop_conv.debug(),
        [&step](messaget::mstreamt &mstream) {
          step.output(mstream);
          mstream << messaget::eom;
        });

      implies_exprt implication(
        assumption,
        step.cond_expr);

      // do the conversion
      try
      {
        step.cond_literal = prop_conv.convert(implication);
      }
      catch(const bitvector_conversion_exceptiont &)
      {
        util_throw_with_nested(
          equation_conversion_exceptiont(
            "Error converting assertions for step", step));
      }

      // store disjunct
      disjuncts.push_back(literal_exprt(!step.cond_literal));
    }
    else if(step.is_assume())
    {
      // the assumptions have been converted before
      // avoid deep nesting of ID_and expressions
      if(assumption.id()==ID_and)
        assumption.copy_to_operands(literal_exprt(step.cond_literal));
      else
        assumption=
          and_exprt(assumption, literal_exprt(step.cond_literal));
    }
  }

  // the below is 'true' if there are no assertions
  prop_conv.set_to_true(disjunction(disjuncts));
}

void symex_target_equationt::convert_function_calls(
  decision_proceduret &dec_proc)
{
  std::size_t argument_count=0;

  for(auto &step : SSA_steps)
    if(!step.ignore)
    {
      step.converted_function_arguments.reserve(step.ssa_function_arguments.size());

      for(const auto &arg : step.ssa_function_arguments)
      {
        if(arg.is_constant() ||
           arg.id()==ID_string_constant)
          step.converted_function_arguments.push_back(arg);
        else
        {
          const irep_idt identifier="symex::args::"+std::to_string(argument_count++);
          symbol_exprt symbol(identifier, arg.type());

          equal_exprt eq(arg, symbol);
          merge_irep(eq);

          dec_proc.set_to(eq, true);
          step.converted_function_arguments.push_back(symbol);
        }
      }
    }
}

void symex_target_equationt::convert_io(
  decision_proceduret &dec_proc)
{
  std::size_t io_count=0;

  for(auto &step : SSA_steps)
    if(!step.ignore)
    {
      for(const auto &arg : step.io_args)
      {
        if(arg.is_constant() ||
           arg.id()==ID_string_constant)
          step.converted_io_args.push_back(arg);
        else
        {
          symbol_exprt symbol;
          symbol.type()=arg.type();
          symbol.set_identifier("symex::io::"+std::to_string(io_count++));

          equal_exprt eq(arg, symbol);
          merge_irep(eq);

          dec_proc.set_to(eq, true);
          step.converted_io_args.push_back(symbol);
        }
      }
    }
}

void symex_target_equationt::merge_ireps(SSA_stept &SSA_step)
{
  merge_irep(SSA_step.guard);

  merge_irep(SSA_step.ssa_lhs);
  merge_irep(SSA_step.ssa_full_lhs);
  merge_irep(SSA_step.original_full_lhs);
  merge_irep(SSA_step.ssa_rhs);

  merge_irep(SSA_step.cond_expr);

  for(auto &step : SSA_step.io_args)
    merge_irep(step);

  for(auto &arg : SSA_step.ssa_function_arguments)
    merge_irep(arg);

  // converted_io_args is merged in convert_io
}

void symex_target_equationt::output(
  std::ostream &out,
  const namespacet &ns) const
{
  for(const auto &step : SSA_steps)
  {
    step.output(ns, out);
    out << "--------------\n";
  }
}

void symex_target_equationt::SSA_stept::output(
  const namespacet &ns,
  std::ostream &out) const
{
  if(source.is_set)
  {
    out << "Thread " << source.thread_nr;

    if(source.pc->source_location.is_not_nil())
      out << " " << source.pc->source_location << '\n';
    else
      out << '\n';
  }

  switch(type)
  {
  case goto_trace_stept::typet::ASSERT:
    out << "ASSERT " << from_expr(ns, source.function, cond_expr) << '\n';
    break;
  case goto_trace_stept::typet::ASSUME:
    out << "ASSUME " << from_expr(ns, source.function, cond_expr) << '\n';
    break;
  case goto_trace_stept::typet::LOCATION:
    out << "LOCATION" << '\n'; break;
  case goto_trace_stept::typet::INPUT:
    out << "INPUT" << '\n'; break;
  case goto_trace_stept::typet::OUTPUT:
    out << "OUTPUT" << '\n'; break;

  case goto_trace_stept::typet::DECL:
    out << "DECL" << '\n';
    out << from_expr(ns, source.function, ssa_lhs) << '\n';
    break;

  case goto_trace_stept::typet::ASSIGNMENT:
    out << "ASSIGNMENT (";
    switch(assignment_type)
    {
    case assignment_typet::HIDDEN:
      out << "HIDDEN";
      break;
    case assignment_typet::STATE:
      out << "STATE";
      break;
    case assignment_typet::VISIBLE_ACTUAL_PARAMETER:
      out << "VISIBLE_ACTUAL_PARAMETER";
      break;
    case assignment_typet::HIDDEN_ACTUAL_PARAMETER:
      out << "HIDDEN_ACTUAL_PARAMETER";
      break;
    case assignment_typet::PHI:
      out << "PHI";
      break;
    case assignment_typet::GUARD:
      out << "GUARD";
      break;
    default:
      {
      }
    }

    out << ")\n";
    break;

  case goto_trace_stept::typet::DEAD:
    out << "DEAD\n"; break;
  case goto_trace_stept::typet::FUNCTION_CALL:
    out << "FUNCTION_CALL\n"; break;
  case goto_trace_stept::typet::FUNCTION_RETURN:
    out << "FUNCTION_RETURN\n"; break;
  case goto_trace_stept::typet::CONSTRAINT:
    out << "CONSTRAINT\n"; break;
  case goto_trace_stept::typet::SHARED_READ:
    out << "SHARED READ\n"; break;
  case goto_trace_stept::typet::SHARED_WRITE:
    out << "SHARED WRITE\n"; break;
  case goto_trace_stept::typet::ATOMIC_BEGIN:
    out << "ATOMIC_BEGIN\n"; break;
  case goto_trace_stept::typet::ATOMIC_END:
    out << "AUTOMIC_END\n"; break;
  case goto_trace_stept::typet::SPAWN:
    out << "SPAWN\n"; break;
  case goto_trace_stept::typet::MEMORY_BARRIER:
    out << "MEMORY_BARRIER\n"; break;
  case goto_trace_stept::typet::GOTO:
    out << "IF " << from_expr(ns, source.function, cond_expr) << " GOTO\n";
    break;

  default: UNREACHABLE;
  }

  if(is_assert() || is_assume() || is_assignment() || is_constraint())
    out << from_expr(ns, source.function, cond_expr) << '\n';

  if(is_assert() || is_constraint())
    out << comment << '\n';

  if(is_shared_read() || is_shared_write())
    out << from_expr(ns, source.function, ssa_lhs) << '\n';

  out << "Guard: " << from_expr(ns, source.function, guard) << '\n';
}

void symex_target_equationt::SSA_stept::output(std::ostream &out) const
{
  if(source.is_set)
  {
    out << "Thread " << source.thread_nr;

    if(source.pc->source_location.is_not_nil())
      out << " " << source.pc->source_location << '\n';
    else
      out << '\n';
  }

  switch(type)
  {
  case goto_trace_stept::typet::ASSERT:
    out << "ASSERT " << format(cond_expr) << '\n';
    break;
  case goto_trace_stept::typet::ASSUME:
    out << "ASSUME " << format(cond_expr) << '\n';
    break;
  case goto_trace_stept::typet::LOCATION:
    out << "LOCATION" << '\n';
    break;
  case goto_trace_stept::typet::INPUT:
    out << "INPUT" << '\n';
    break;
  case goto_trace_stept::typet::OUTPUT:
    out << "OUTPUT" << '\n';
    break;

  case goto_trace_stept::typet::DECL:
    out << "DECL" << '\n';
    out << format(ssa_lhs) << '\n';
    break;

  case goto_trace_stept::typet::ASSIGNMENT:
    out << "ASSIGNMENT (";
    switch(assignment_type)
    {
    case assignment_typet::HIDDEN:
      out << "HIDDEN";
      break;
    case assignment_typet::STATE:
      out << "STATE";
      break;
    case assignment_typet::VISIBLE_ACTUAL_PARAMETER:
      out << "VISIBLE_ACTUAL_PARAMETER";
      break;
    case assignment_typet::HIDDEN_ACTUAL_PARAMETER:
      out << "HIDDEN_ACTUAL_PARAMETER";
      break;
    case assignment_typet::PHI:
      out << "PHI";
      break;
    case assignment_typet::GUARD:
      out << "GUARD";
      break;
    default:
    {
    }
    }

    out << ")\n";
    break;

  case goto_trace_stept::typet::DEAD:
    out << "DEAD\n";
    break;
  case goto_trace_stept::typet::FUNCTION_CALL:
    out << "FUNCTION_CALL\n";
    break;
  case goto_trace_stept::typet::FUNCTION_RETURN:
    out << "FUNCTION_RETURN\n";
    break;
  case goto_trace_stept::typet::CONSTRAINT:
    out << "CONSTRAINT\n";
    break;
  case goto_trace_stept::typet::SHARED_READ:
    out << "SHARED READ\n";
    break;
  case goto_trace_stept::typet::SHARED_WRITE:
    out << "SHARED WRITE\n";
    break;
  case goto_trace_stept::typet::ATOMIC_BEGIN:
    out << "ATOMIC_BEGIN\n";
    break;
  case goto_trace_stept::typet::ATOMIC_END:
    out << "AUTOMIC_END\n";
    break;
  case goto_trace_stept::typet::SPAWN:
    out << "SPAWN\n";
    break;
  case goto_trace_stept::typet::MEMORY_BARRIER:
    out << "MEMORY_BARRIER\n";
    break;
  case goto_trace_stept::typet::GOTO:
    out << "IF " << format(cond_expr) << " GOTO\n";
    break;

  default:
    UNREACHABLE;
  }

  if(is_assert() || is_assume() || is_assignment() || is_constraint())
    out << format(cond_expr) << '\n';

  if(is_assert() || is_constraint())
    out << comment << '\n';

  if(is_shared_read() || is_shared_write())
    out << format(ssa_lhs) << '\n';

  out << "Guard: " << format(guard) << '\n';
}

/// Check that the SSA step is well-formed
/// \param ns: namespace to lookup identifiers
/// \param vm: validation mode to be used for reporting failures
void symex_target_equationt::SSA_stept::validate(
  const namespacet &ns,
  const validation_modet vm) const
{
  validate_full_expr(guard, ns, vm);

  switch(type)
  {
  case goto_trace_stept::typet::ASSERT:
  case goto_trace_stept::typet::ASSUME:
  case goto_trace_stept::typet::GOTO:
  case goto_trace_stept::typet::CONSTRAINT:
    validate_full_expr(cond_expr, ns, vm);
    break;
  case goto_trace_stept::typet::DECL:
    validate_full_expr(ssa_lhs, ns, vm);
    validate_full_expr(ssa_full_lhs, ns, vm);
    validate_full_expr(original_full_lhs, ns, vm);
    break;
  case goto_trace_stept::typet::ASSIGNMENT:
    validate_full_expr(ssa_lhs, ns, vm);
    validate_full_expr(ssa_full_lhs, ns, vm);
    validate_full_expr(original_full_lhs, ns, vm);
    validate_full_expr(ssa_rhs, ns, vm);
    DATA_CHECK(
      vm,
      base_type_eq(ssa_lhs.get_original_expr().type(), ssa_rhs.type(), ns),
      "Type inequality in SSA assignment\nlhs-type: " +
        ssa_lhs.get_original_expr().type().id_string() +
        "\nrhs-type: " + ssa_rhs.type().id_string());
    break;
  case goto_trace_stept::typet::INPUT:
  case goto_trace_stept::typet::OUTPUT:
    for(const auto &expr : io_args)
      validate_full_expr(expr, ns, vm);
    break;
  case goto_trace_stept::typet::FUNCTION_CALL:
    for(const auto &expr : ssa_function_arguments)
      validate_full_expr(expr, ns, vm);
  case goto_trace_stept::typet::FUNCTION_RETURN:
  {
    const symbolt *symbol;
    DATA_CHECK(
      vm,
      called_function.empty() || !ns.lookup(called_function, symbol),
      "unknown function identifier " + id2string(called_function));
  }
  break;
  case goto_trace_stept::typet::NONE:
  case goto_trace_stept::typet::LOCATION:
  case goto_trace_stept::typet::DEAD:
  case goto_trace_stept::typet::SHARED_READ:
  case goto_trace_stept::typet::SHARED_WRITE:
  case goto_trace_stept::typet::SPAWN:
  case goto_trace_stept::typet::MEMORY_BARRIER:
  case goto_trace_stept::typet::ATOMIC_BEGIN:
  case goto_trace_stept::typet::ATOMIC_END:
    break;
  }
}

irep_idt symex_target_equationt::SSA_stept::get_property_id() const
{
  PRECONDITION(is_assert());

  irep_idt property_id;

  if(source.pc->is_assert())
  {
    property_id = source.pc->source_location.get_property_id();
  }
  else if(source.pc->is_goto())
  {
    // this is likely an unwinding assertion
    property_id = id2string(source.pc->source_location.get_function()) +
                  ".unwind." + std::to_string(source.pc->loop_number);
  }
  else if(source.pc->is_function_call())
  {
    // this is likely a recursion unwinding assertion
    property_id =
      id2string(source.pc->source_location.get_function()) + ".recursion";
  }
  else
  {
    UNREACHABLE;
  }

  return property_id;
}
